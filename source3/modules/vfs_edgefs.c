/*
   Unix SMB/CIFS implementation.

   Wrap EdgeFS CCOW API calls in vfs functions.

   Copyright (c) 2020 Dmitry Yusupov <dmitry@highpeakdata.com>

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

/**
 * A Samba VFS module for EdgeFS, based on EdgeFS's libccowfsio API.
 * This is a "bottom" vfs module (not something to be stacked on top of
 * another module), and translates (most) calls to the closest actions
 * available in libccowfsio.
 */

#define	__ERROR__XX__NEVER_USE_SPRINTF__
#define	__ERROR__XX__NEVER_USE_STRCPY___

#include "ccowfsio.h"
#include "includes.h"
#include "smbd/smbd.h"
#include <stdio.h>
#include "lib/util/dlinklist.h"
#include "lib/util/tevent_unix.h"
#include "smbd/globals.h"
#include "lib/util/sys_rw.h"
#include "smbprofile.h"
#include "modules/posixacl_xattr.h"
#include "lib/pthreadpool/pthreadpool_tevent.h"

#define	IF_STR_EMPTY(s)	((s)[0] == '\0')
#define	IF_STR_DOT(s)	((s)[0] == '.' && (s)[1] == '\0')
#define	IF_STR_DOTDOT(s) ((s)[0] == '.' && (s)[1] == '.' && (s)[2] == '\0')

/* pre-opened ci_t */
static struct edgefs_preopened {
	char *bucketUri;
	char *ccowConfFile;
	char *connectpath;
	ci_t *fs;
	int ref;
	struct edgefs_preopened *next, *prev;
} *edgefs_preopened;

struct edgefs_conn_priv {
	ci_t *ci;
	char *cwd;
};

#define	HANDLE_CI(h)	(((struct edgefs_conn_priv *)(h)->data)->ci)
#define	HANDLE_CWD(h)	(((struct edgefs_conn_priv *)(h)->data)->cwd)

struct edgefs_open_handle {
	int flags;
	char *full_path;
	char *vfs_path;
	DIR *dir;
	ccow_fsio_file_t *file;
};

#define	CCOW_FSIO_DIRENT_PREFETCH 64 /* Like MAX_READIR_ENTRIES_AT_A_TIME. */
struct vfs_edgefs_dir {
	inode_t dir_ino;
	size_t pos; /* Absolute readdir position. */
	fsio_dir_entry dirents[CCOW_FSIO_DIRENT_PREFETCH];
	int dirents_cnt; /* Prefetched last time */
	int current_of_dirents; /* Current of dirents passed to readdir. */
	bool eof; /* Last prefetch complete list. */
	struct dirent *dirent;
};

static int
ifDot(char *s, int p1, int p2)
{

	if (p1 == -1)
		return (0);
	if (p2 == -1)
		return (0);
	if ((p2 - p1) != 2)
		return (0);
	if (s[p1+1] == '.')
		return (1);
	return (0);
}

static int
ifDotDot(char *s, int p1, int p2)
{

	if (p1 == -1)
		return (0);
	if (p2 == -1)
		return (0);
	if ((p2 - p1) != 3)
		return (0);
	if ((s[p1+1] == '.') && (s[p1+2] == '.'))
		return (1);
	return (0);
}

#define	xSTRCPY(dst, src) memmove((dst), (src), strlen((src)) + 1);

static int
normalize_path(char *n)
{
	int i, sl[3];

	/* Strip extra slashes. */
	for (i = 1; i < strlen(n); i++) {
		if (n[i - 1] == '/' && n[i] == '/') {
			xSTRCPY(&n[i], &n[i + 1]);
			i--;
		}
	}
	if (strcmp(n, "/..") == 0)
		return (-1);

	/* Strip double dot with its parent. */
reset:
	sl[0] = sl[1] = sl[2] = -1;
	for (i = 0; i < strlen(n); i++) {
		if (n[i] != '/')
			continue;
		sl[0] = sl[1];
		sl[1] = sl[2];
		sl[2] = i;
		if (ifDot(n, sl[1], sl[2])) {
			xSTRCPY(&n[sl[1]+1], &n[sl[2]+1]);
			goto reset;
		}
		if (sl[0] != -1 && ifDotDot(n, sl[1], sl[2])) {
			xSTRCPY(&n[sl[0]+1], &n[sl[2]+1]);
			goto reset;
		}
	}

	if (sl[2] != -1 && ifDot(n, sl[2], strlen(n))) {
		xSTRCPY(&n[sl[2]], &n[strlen(n)]);
	} else if (sl[0] != -1 && ifDotDot(n, sl[2], strlen(n))) {
		xSTRCPY(&n[sl[1]], &n[strlen(n)]);
	}
	if (strlen(n) > 0 && n[strlen(n) - 1] == '/')
		n[strlen(n) - 1] = '\0';

	return (0);
}

static int
vfs_edgefs_smb_fname2inode(struct vfs_handle_struct *handle,
    struct smb_filename *smb_fname, inode_t *inode)
{
	char *name;
	char *path;
	int i, l, ret = 0;

	name = smb_fname->base_name;
	DBG_ERR("############@@@@@@2 file \"%s\", l=%d\n", name, l);
	if (name[0] == '/') {
		path = strdup(name); // XXX Allocator
		if (path == NULL)
			return (errno);
	} else {
		ret = asprintf(&path, "%s/%s", HANDLE_CWD(handle), name);
		if (ret == -1)
			return (errno);
	}
#if 0
	l = strlen(path);
	if (l > 2) {
		if (strcmp(&path[l-3], "/..") == 0) {
			/* cut one dir in path end. */
			for (i = l - 4; i > 0; i-- ) {
				if (path[i] == '/') {
					path[i] = '\0';
					break;
				}
			}
		}
	}
	l = strlen(path);
	DBG_ERR("############ file \"%s\", l=%d\n", path, l);
	if (l > 0 && path[l - 1] == '.')
		path[l - 1] = '\0';
#else
	if (normalize_path(path) != 0) {
		DBG_ERR("file path error \"%s\".\n", path);
		errno = EINVAL;
		goto fail;
	}
#endif
	DBG_ERR("############++++ file \"%s\"\n", path);
	name = path;

	if (strstr(name, handle->conn->connectpath) != name) {
		DBG_ERR("Not a VFS file \"%s\"\n", name);
		ret = EINVAL;
		goto fail;
	} else {
		name += strlen(handle->conn->connectpath);
	}
	DBG_INFO("%d: VFS file \"%s\".\n", __LINE__, name);

	ret = ccow_fsio_find(HANDLE_CI(handle), name, inode);
	if (ret != 0 && ret != ENOENT)
		DBG_ERR("%d: query VFS file \"%s\" failed.\n", __LINE__, name);
fail:
	free(path);
	return (ret);
}

/**
 * Helper to convert struct stat to struct stat_ex.
 */
static void
smb_stat_ex_from_stat(struct stat_ex *dst, const struct stat *src)
{
	ZERO_STRUCTP(dst);

	dst->st_ex_dev = src->st_dev;
	dst->st_ex_ino = src->st_ino;
	dst->st_ex_mode = src->st_mode;
	dst->st_ex_nlink = src->st_nlink;
	dst->st_ex_uid = src->st_uid;
	dst->st_ex_gid = src->st_gid;
	dst->st_ex_rdev = src->st_rdev;
	dst->st_ex_size = src->st_size;
	dst->st_ex_atime.tv_sec = src->st_atime;
	dst->st_ex_mtime.tv_sec = src->st_mtime;
	dst->st_ex_ctime.tv_sec = src->st_ctime;
	dst->st_ex_btime.tv_sec = src->st_mtime;
	dst->st_ex_blksize = src->st_blksize;
	dst->st_ex_blocks = src->st_blocks;
	dst->st_ex_file_id = dst->st_ex_ino;
	dst->st_ex_iflags |= ST_EX_IFLAG_CALCULATED_FILE_ID;
#ifdef STAT_HAVE_NSEC
	dst->st_ex_atime.tv_nsec = src->st_atime_nsec;
	dst->st_ex_mtime.tv_nsec = src->st_mtime_nsec;
	dst->st_ex_ctime.tv_nsec = src->st_ctime_nsec;
	dst->st_ex_btime.tv_nsec = src->st_mtime_nsec;
#endif
	dst->st_ex_itime = dst->st_ex_btime;
	dst->st_ex_iflags |= ST_EX_IFLAG_CALCULATED_ITIME;
}

static int
edgefs_set_preopened(const char *bucketUri, const char *ccowConfFile,
    const char *connectpath, ci_t *fs)
{
	struct edgefs_preopened *entry = NULL;

	entry = talloc_zero(NULL, struct edgefs_preopened);
	if (!entry) {
		errno = ENOMEM;
		return -1;
	}

	entry->bucketUri = talloc_strdup(entry, bucketUri);
	if (!entry->bucketUri) {
		talloc_free(entry);
		errno = ENOMEM;
		return -1;
	}

	entry->ccowConfFile = talloc_strdup(entry, ccowConfFile);
	if (entry->ccowConfFile == NULL) {
		talloc_free(entry);
		errno = ENOMEM;
		return -1;
	}

	entry->connectpath = talloc_strdup(entry, connectpath);
	if (entry->connectpath == NULL) {
		talloc_free(entry);
		errno = ENOMEM;
		return -1;
	}

	entry->fs = fs;
	entry->ref = 1;

	DLIST_ADD(edgefs_preopened, entry);

	return 0;
}

static ci_t *
edgefs_find_preopened(const char *bucketUri, const char *ccowConfFile,
    const char *connectpath)
{
	struct edgefs_preopened *entry = NULL;

	for (entry = edgefs_preopened; entry; entry = entry->next) {
		if (strcmp(entry->bucketUri, bucketUri) == 0 &&
		    strcmp(entry->ccowConfFile, ccowConfFile) == 0 &&
		    strcmp(entry->connectpath, connectpath) == 0)
		{
			entry->ref++;
			return entry->fs;
		}
	}

	return NULL;
}

static void
edgefs_clear_preopened(ci_t *fs)
{
	struct edgefs_preopened *entry = NULL;

	for (entry = edgefs_preopened; entry; entry = entry->next) {
		if (entry->fs != fs)
			continue;
		if (--entry->ref)
			return;

		DLIST_REMOVE(edgefs_preopened, entry);

		ccow_fsio_delete_export(entry->fs);
		ccow_fsio_ci_free(entry->fs);
		talloc_free(entry);
	}
}

static int
edgefs_up(void *args, inode_t inode, uint64_t ccow_fsio_up_flags)
{

	return (0);
}

/* Disk Operations */
static int
vfs_edgefs_connect(struct vfs_handle_struct *handle, const char *service,
    const char *user)
{
	const char *bucketUri, *ccowConfFile, *logfile;
	struct stat stat;
	inode_t inode;
	int loglevel;
	ci_t *fs = NULL;
	int ret = 0;
	struct edgefs_conn_priv *priv;

	logfile = lp_parm_const_string(SNUM(handle->conn),
	    "edgefs", "logfile", NULL);
	loglevel = lp_parm_int(SNUM(handle->conn),
	    "edgefs", "loglevel", -1);
	ccowConfFile = lp_parm_const_string(SNUM(handle->conn),
	    "edgefs", "ccowConfigFile", NULL);
	bucketUri = lp_parm_const_string(SNUM(handle->conn),
	    "edgefs", "bucketUri", NULL);

	if (ccowConfFile == NULL)
		ccowConfFile = "/opt/nedge/etc/ccow/ccow.json";
	if (bucketUri == NULL) {
		DBG_ERR("%d: bucketUri can't be empty.\n", __LINE__);
		return (-1);
	}

	handle->data = talloc_zero(handle->conn, struct edgefs_conn_priv);
	if (handle->data == NULL) {
		DBG_ERR("talloc_zero() failed\n");
		errno = ENOMEM;
		return -1;
	}

	HANDLE_CWD(handle) = strdup("/");
	if (HANDLE_CWD(handle) == NULL) {
		ret = errno;
		talloc_free(handle->data);
		return (ret);
	}

	DBG_INFO("Connect CCOW FSIO context, bucket: %s, config: %s. "
	    "At path: %s\n", bucketUri, ccowConfFile,
	    handle->conn->connectpath);

	fs = edgefs_find_preopened(bucketUri, ccowConfFile,
	    handle->conn->connectpath);
	if (fs) {
		goto done;
	}

	/* Allocate share. */
	fs = ccow_fsio_ci_alloc();
	if (fs == NULL) {
		DBG_ERR("Failed to allocate CCOW FSIO context.\n");
		ret = ENOMEM;
		goto done;
	}
	/* Init share. */
	ret = ccow_fsio_create_export(fs, (char *)bucketUri,
	    (char *)ccowConfFile, 4096, edgefs_up, NULL);
	if (ret != 0) {
		DBG_ERR("Failed to create share for bucket \"%s\"\n",
		    bucketUri);
		goto free_ci;
	}

	ret = ccow_fsio_get_file_stat(fs, CCOW_FSIO_ROOT_INODE, &stat);
	if (ret == ENOENT) {
		/*
		 * XXX We have to get default params (mode, uid, gid, etc) or
		 * policy on what to do if no file attr for inode
		 * CCOW_FSIO_ROOT_INODE.
		 */
		stat.st_ino = CCOW_FSIO_ROOT_INODE;
		stat.st_size = stat.st_gid = stat.st_uid = 0;
		stat.st_mode = S_IFDIR | 0755;
		ccow_fsio_mkdir(fs, CCOW_FSIO_ROOT_INODE, ".edgefs.smb.test",
		    stat.st_mode, stat.st_uid, stat.st_gid, &inode);
		ccow_fsio_delete(fs, CCOW_FSIO_ROOT_INODE, ".edgefs.smb.test");
		ccow_fsio_set_file_stat(fs, CCOW_FSIO_ROOT_INODE, &stat);
		ret = ccow_fsio_get_file_stat(fs, CCOW_FSIO_ROOT_INODE, &stat);
	}
	if (ret != 0) {
		DBG_ERR("ccow_fsio_get_file_stat return \"%d\"\n",
		    ret);
		ret = EINVAL;
		goto del_exp;
	}

	HANDLE_CI(handle) = fs;

	ret = edgefs_set_preopened(bucketUri, ccowConfFile,
	    handle->conn->connectpath, fs);
	if (ret < 0) {
		DEBUG(0, ("%s: Failed to register share for bucket (%s)\n",
		    bucketUri, strerror(errno)));
		goto del_exp;
	}

	goto done;

del_exp:
	ccow_fsio_delete_export(fs);
free_ci:
	ccow_fsio_ci_free(fs);

done:
	return (ret);
}

static void
vfs_edgefs_disconnect(struct vfs_handle_struct *handle)
{
	ci_t *fs;

	fs = HANDLE_CI(handle);

	edgefs_clear_preopened(fs);
}

static uint64_t
vfs_edgefs_disk_free(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, uint64_t *bsize_p, uint64_t *dfree_p,
    uint64_t *dsize_p)
{
	fsio_fsinfo_t fsinfo;
	struct stat stat;
	size_t chunkSize;
	int ret;

	ret = ccow_fsio_fsinfo(HANDLE_CI(handle), &fsinfo);
	if (ret < 0) {
		return -1;
	}
	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), CCOW_FSIO_ROOT_INODE,
	    &stat);
	if (ret < 0) {
		return -1;
	}

	chunkSize = stat.st_blksize ? stat.st_blksize : 4096;

	if (bsize_p != NULL) {
		/* Block size */
		*bsize_p = (uint64_t)chunkSize;
	}
	if (dfree_p != NULL) {
		/* Available Block units */
		*dfree_p = (uint64_t)(fsinfo.avail_bytes / chunkSize);
	}
	if (dsize_p != NULL) {
		/* Total Block units */
		*dsize_p = (uint64_t)(fsinfo.total_bytes / chunkSize);
	}

	return (uint64_t)(fsinfo.avail_bytes / chunkSize);
}

static int
vfs_edgefs_get_quota(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, enum SMB_QUOTA_TYPE qtype, unid_t id,
    SMB_DISK_QUOTA *qt)
{
	/* TODO */
	errno = ENOSYS;
	return -1;
}

static int
vfs_edgefs_set_quota(struct vfs_handle_struct *handle,
    enum SMB_QUOTA_TYPE qtype, unid_t id, SMB_DISK_QUOTA *qt)
{
	/* TODO */
	errno = ENOSYS;
	return -1;
}

static int
vfs_edgefs_statvfs(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname,
    struct vfs_statvfs_struct *vfs_statvfs)
{
	fsio_fsinfo_t fsinfo;
	struct stat stat;
	size_t chunkSize;
	int ret;

	ret = ccow_fsio_fsinfo(HANDLE_CI(handle), &fsinfo);
	if (ret < 0) {
		DEBUG(0, ("edgefs_statvfs(%s) failed: %s\n",
			    smb_fname->base_name, strerror(errno)));
		return -1;
	}

	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), CCOW_FSIO_ROOT_INODE,
	    &stat);
	if (ret < 0) {
		return -1;
	}

	chunkSize = stat.st_blksize ? stat.st_blksize : 4096;

	ZERO_STRUCTP(vfs_statvfs);

	vfs_statvfs->OptimalTransferSize = chunkSize;
	vfs_statvfs->BlockSize = chunkSize;
	vfs_statvfs->TotalBlocks = (fsinfo.total_bytes / chunkSize);
	vfs_statvfs->BlocksAvail = (fsinfo.avail_bytes / chunkSize);
	vfs_statvfs->UserBlocksAvail = (fsinfo.avail_bytes / chunkSize);
	vfs_statvfs->TotalFileNodes = (fsinfo.total_files / chunkSize);
	vfs_statvfs->FreeFileNodes = (fsinfo.free_files / chunkSize);
	vfs_statvfs->FsIdentifier = 0ULL; //XXX
	vfs_statvfs->FsCapabilities = FILE_CASE_SENSITIVE_SEARCH |
	    FILE_CASE_PRESERVED_NAMES;

	return ret;
}

static uint32_t
vfs_edgefs_fs_capabilities(struct vfs_handle_struct *handle,
		enum timestamp_set_resolution *p_ts_res)
{
DBG_INFO("%s:%d\n", __func__, __LINE__);
	uint32_t caps = FILE_CASE_SENSITIVE_SEARCH | FILE_CASE_PRESERVED_NAMES;

	caps |= FILE_SUPPORTS_SPARSE_FILES;

	/* TODO: Can be read-only (like S3 view). */
#ifdef STAT_HAVE_NSEC
	*p_ts_res = TIMESTAMP_SET_NT_OR_BETTER;
#endif

	return caps;
}

static DIR *
vfs_edgefs_opendir(struct vfs_handle_struct *handle,
		const struct smb_filename *smb_fname,
		const char *mask, uint32_t attributes)
{
	struct vfs_edgefs_dir *dir;
	inode_t inode;
	int ret;

	START_PROFILE(syscall_opendir);
	ret = vfs_edgefs_smb_fname2inode(handle, smb_fname, &inode);
	if (ret != 0) {
		errno = ret;
		goto fail;
	}
	dir = SMB_CALLOC_ARRAY(struct vfs_edgefs_dir, 1);
	if (dir == NULL) {
		errno = ENOMEM;
		goto fail;
	}
	dir->dir_ino = inode;
	dir->dirents_cnt = 0;
	dir->dirent = NULL;
fail:
	if (dir == NULL) {
		DEBUG(0, ("edgefs_opendir(%s) failed: %s\n",
			    smb_fname->base_name, strerror(errno)));
	}

	END_PROFILE(syscall_opendir);
	return (DIR *) dir;
}

static ccow_fsio_file_t *
vfs_edgefs_fetch_file(struct vfs_handle_struct *handle, files_struct *fsp)
{
	ccow_fsio_file_t *file;
	struct edgefs_open_handle *oh;

	oh = (struct edgefs_open_handle *)VFS_FETCH_FSP_EXTENSION(handle, fsp);
	if (oh == NULL) {
		DBG_INFO("Failed to fetch fsp extension\n");
		return NULL;
	}
	file = oh->file;
	if (file == NULL) {
		DBG_INFO("Empty ccow_fsio_file_t pointer\n");
		return NULL;
	}

	return file;
}

static struct vfs_edgefs_dir *
vfs_edgefs_fetch_dir(struct vfs_handle_struct *handle, files_struct *fsp)
{
	struct edgefs_open_handle *oh;
	struct vfs_edgefs_dir *dir;

	oh = (struct edgefs_open_handle *)VFS_FETCH_FSP_EXTENSION(handle, fsp);
	if (oh == NULL) {
		DBG_INFO("Failed to fetch fsp extension\n");
		return NULL;
	}
	dir = (struct vfs_edgefs_dir *)oh->dir;
	if (dir == NULL) {
		DBG_INFO("Empty DIR pointer\n");
		return NULL;
	}

	return dir;
}

static DIR *
vfs_edgefs_fdopendir(struct vfs_handle_struct *handle,
		files_struct *fsp, const char *mask,
		uint32_t attributes)
{
	DIR *dir;
	DEBUG(10, ("Entering with fsp->fsp_name->base_name '%s'\n",
		   fsp->fsp_name->base_name));
	dir = vfs_edgefs_opendir(handle, fsp->fsp_name, mask, attributes);

	return dir;
}

static int
vfs_edgefs_closedir(struct vfs_handle_struct *handle, DIR *dirp)
{
DBG_INFO("%s:%d\n", __func__, __LINE__);
	struct vfs_edgefs_dir *dir;
	int i, ret;

	ret = 0;
	START_PROFILE(syscall_closedir);
	dir = (struct vfs_edgefs_dir *)dirp;
DBG_INFO("%d dir inode=%lu\n", __LINE__, dir->dir_ino);
DBG_INFO("%d cnt=%d\n", __LINE__, dir->dirents_cnt);
	for (i = 0; i < dir->dirents_cnt; i++) {
		DBG_INFO("ent[%d].name @%p\n", i, &dir->dirents[i].name);
		if (dir->dirents[i].name == NULL)
			continue;
		DBG_INFO("ent[%d].name = \"%s\"\n", i, dir->dirents[i].name);
		SAFE_FREE(dir->dirents[i].name);
		dir->dirents[i].name = NULL;
	}
	if (dir->dirent) {
DBG_INFO("%d Free current dirent.\n", __LINE__);
		//TALLOC_FREE(dir->dirent);
		dir->dirent = NULL;
	}
	SAFE_FREE(dir);
	END_PROFILE(syscall_closedir);

	return ret;
}

static int
edgefs_readdir_cb4(inode_t parent, fsio_dir_entry *de, uint64_t p, void *ptr)
{
	struct vfs_edgefs_dir *dir;
	char *n;
	int i;

	dir = (struct vfs_edgefs_dir *)ptr;
	for (i = 0; i < p; i++) {
		n = strdup(de[i].name);
		if (n == NULL)
			return (errno);
		dir->dirents[dir->dirents_cnt].name = n;
		dir->dirents[dir->dirents_cnt].inode = de[i].inode;
		DBG_INFO("%d %s ==> %lu #%d.\n", __LINE__, n, de[i].inode, dir->dirents_cnt);
		dir->dirents_cnt++;
		if (dir->dirents_cnt >= CCOW_FSIO_DIRENT_PREFETCH)
			return (1);
	}

	return (0);
}

static struct dirent *
vfs_edgefs_readdir(struct vfs_handle_struct *handle, DIR *dirp,
    SMB_STRUCT_STAT *sbuf)
{
	static char direntbuf[512];
	int i, ret;
	inode_t parent_ino;
	bool eof;
	char *n;

	struct vfs_edgefs_dir *dir;
	dir = (struct vfs_edgefs_dir *)dirp;

	DBG_INFO(":%d sbuf=%p dir_ino=%lu, cnt=%d, of: %d, pos: %lu, eof: %d\n",
	    __LINE__, sbuf, dir->dir_ino, dir->dirents_cnt,
	    dir->current_of_dirents, dir->pos, dir->eof);

	START_PROFILE(syscall_readdir);
	parent_ino = dir->dir_ino;
	DBG_INFO(":%d cur=%d, cnt=%d, eof=%d.\n", __LINE__,
	    dir->current_of_dirents, dir->dirents_cnt, dir->eof);

	if (dir->dirents_cnt == 0 || /* If not fetched yet. */
	    /* Or if need next to top entry, but not if we reach eof. */
	    (dir->current_of_dirents == dir->dirents_cnt && !dir->eof)) {

		DBG_INFO(":%d Cleanup before fetch next portion.\n", __LINE__);
		n = (dir->dirents_cnt > 0)?
		    strdup(dir->dirents[dir->dirents_cnt - 1].name):"";
		if (n == NULL)
			return (errno);

		/* Free names allocated by strdup.  */
		for (i = 0; i < dir->dirents_cnt; i++) {
			if (dir->dirents[i].name == NULL)
				continue;
			free(dir->dirents[i].name);
			dir->dirents[i].name = NULL;
		}

		/* Reset counters before fetch. */
		dir->dirents_cnt = 0;
		dir->current_of_dirents = 0;
		DBG_INFO(":%d Fetch next portion (dir: %lu, pos: \"%s\").\n",
		    __LINE__, parent_ino, n);

		ret = ccow_fsio_readdir_cb4(HANDLE_CI(handle), parent_ino,
		    edgefs_readdir_cb4, n, (void *)dir, &eof);
		if (n[0] != '\0')
			free(n);
		if (ret != 0) {
			errno = ret;
			return (NULL);
		}

		DBG_INFO("%d Got %d new entries.\n", __LINE__, dir->dirents_cnt);
		if (eof)
			dir->eof = true;
	}
	if (dir->current_of_dirents >= dir->dirents_cnt) {
		DBG_INFO("%d %d >= %d. Ret NULL\n", __LINE__,
		    dir->current_of_dirents, dir->dirents_cnt);
		return (NULL);
	}
	if (dir->dirent) {
		//TALLOC_FREE(dir->dirent);
		dir->dirent = NULL;
	}

	dir->dirent = talloc_size(talloc_tos(), sizeof(struct dirent) +
	    strlen(dir->dirents[dir->current_of_dirents].name) + 1);
	if (!dir->dirent) {
		errno = ENOMEM;
		return NULL;
	}

	talloc_set_name_const(dir->dirent, "struct dirent");
	memcpy(&dir->dirent->d_name, dir->dirents[dir->current_of_dirents].name,
	    strlen(dir->dirents[dir->current_of_dirents].name)+1);
	dir->dirent->d_fileno = dir->dirents[dir->current_of_dirents].inode;
	dir->dirent->d_off = dir->pos;
	DBG_INFO("%d parent: %lu Return \"%s\"(ino: %lu) at [%lu]\n", __LINE__,
	    parent_ino, dir->dirent->d_name, dir->dirent->d_fileno, dir->pos);
	dir->current_of_dirents++;
	dir->pos++;

	if ((ret < 0) || (dir->dirent == NULL)) {
		END_PROFILE(syscall_readdir);
		return NULL;
	}

	if (sbuf)
		SET_STAT_INVALID(*sbuf);

	END_PROFILE(syscall_readdir);
	return (dir->dirent);
}

static long
vfs_edgefs_telldir(struct vfs_handle_struct *handle, DIR *dirp)
{
	struct vfs_edgefs_dir *dir;
	long ret;

	START_PROFILE(syscall_telldir);
	dir = (struct vfs_edgefs_dir *)dirp;
	ret = dir->pos;
	END_PROFILE(syscall_telldir);

	return ret;
}

static void
vfs_edgefs_seekdir(struct vfs_handle_struct *handle, DIR *dirp, long offset)
{
	struct vfs_edgefs_dir *dir;

	START_PROFILE(syscall_seekdir);
	dir = (struct vfs_edgefs_dir *)dirp;
	int base = dir->pos - dir->current_of_dirents;
	int end = base + dir->dirents_cnt;
	if (base <= offset && offset < end) {
		dir->pos = offset;
		dir->current_of_dirents = offset - base;
	} else {
		/* XXX Do we really need to fetch another dirent portion? */
	}

	END_PROFILE(syscall_seekdir);
}

static void
vfs_edgefs_rewinddir(struct vfs_handle_struct *handle, DIR *dirp)
{
DBG_INFO("%s:%d\n", __func__, __LINE__);
	struct vfs_edgefs_dir *dir;
	START_PROFILE(syscall_rewinddir);
	dir = (struct vfs_edgefs_dir *)dirp;
	dir->pos = 0;
	END_PROFILE(syscall_rewinddir);
}

static int
vfs_edgefs_mkdir(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, mode_t mode)
{
DBG_INFO("%s:%d\n", __func__, __LINE__);
	uint16_t uid, gid;
	char *parent_path;
	char *name;
	inode_t parent;
	int ret;
	TALLOC_CTX *frame;
	struct smb_filename tmp;

	frame = talloc_stackframe();

	uid = gid = 0; //XXX
	START_PROFILE(syscall_mkdir);
	if (!parent_dirname(frame, (const char *)smb_fname->base_name,
		    &parent_path, (const char **)&name)) {
		errno = ENOMEM;
		goto fail;
	}
	tmp.base_name = parent_path;
	ret = vfs_edgefs_smb_fname2inode(handle, &tmp, &parent);
	if (ret != 0) {
		DBG_ERR("Can't find parent dir \"%s\". error=%d\n",
		    parent_path, ret);
		goto fail;
	}
	ret = ccow_fsio_mkdir(HANDLE_CI(handle), parent, name, mode, uid, gid,
	    NULL);
	if (ret != 0) {
		DBG_ERR("Can't create dir \"%s/%s\". error=%d\n", parent_path,
		    name, ret);
	}
fail:
	TALLOC_FREE(frame);
	END_PROFILE(syscall_mkdir);

	return ret;
}

static int
vfs_edgefs_unlink(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname)
{
DBG_INFO("%s:%d\n", __func__, __LINE__);
	char *parent_path;
	char *name;
	inode_t parent;
	int ret;
	TALLOC_CTX *frame;
	struct smb_filename tmp;

	frame = talloc_stackframe();

	START_PROFILE(syscall_unlink);
	if (!parent_dirname(frame, (const char *)smb_fname->base_name,
		    &parent_path, (const char **)&name)) {
		errno = ENOMEM;
		goto fail;
	}
DBG_INFO("%d: parent=%s, name=%s\n", __LINE__, parent_path, name);

	tmp.base_name = parent_path;
	ret = vfs_edgefs_smb_fname2inode(handle, &tmp, &parent);
	if (ret != 0) {
		errno = ret;
		ret = -1;
		goto fail;
	}
	ret = ccow_fsio_unlink(HANDLE_CI(handle), parent, name);
DBG_INFO("%d: ccow_fsio_unlink(hdl, parent_ino=%lu, name=%s) return %d\n",
    __LINE__, parent, name, ret);
fail:
	TALLOC_FREE(frame);
	END_PROFILE(syscall_unlink);

	return ret;
}

static int
vfs_edgefs_open(struct vfs_handle_struct *handle,
    struct smb_filename *smb_fname, files_struct *fsp, int flags, mode_t mode)
{
	struct edgefs_open_handle *p_tmp;
	ccow_fsio_file_t *file;
	char *fname;
	DIR *dir;
	int ret;

	START_PROFILE(syscall_open);

	p_tmp = VFS_ADD_FSP_EXTENSION(handle, fsp, struct edgefs_open_handle,
	    NULL);
	if (p_tmp == NULL) {
		errno = ENOMEM;
		goto fail;
	}

	p_tmp->flags = flags;
	p_tmp->dir = NULL;
	p_tmp->file = NULL;
	if (flags & O_DIRECTORY) {
		dir = vfs_edgefs_opendir(handle, smb_fname, "", 0);
		p_tmp->dir = dir;
	} else {
		fname = smb_fname->base_name;
		ret = asprintf(&fname, "%s/%s", HANDLE_CWD(handle),	// XXX A
		    (IF_STR_DOT(fname))?"":fname);
		if (ret == -1)
			return (errno);
		p_tmp->full_path = fname;
		fname += strlen(handle->conn->connectpath);
		p_tmp->vfs_path = fname;
		if (flags & O_CREAT) {
			inode_t p;
			ret = ccow_fsio_find(HANDLE_CI(handle),
			    HANDLE_CWD(handle) +
			    strlen(handle->conn->connectpath), &p);
			ret = ccow_fsio_touch(HANDLE_CI(handle), p,
			    smb_fname->base_name, mode, 0, 0, NULL);
		}
		ret = ccow_fsio_open(HANDLE_CI(handle), fname, &file, flags);
		if (ret != 0) {
			errno = ret;
			goto fail;
		}
		p_tmp->file = file;
	}

	END_PROFILE(syscall_open);
	return 0;
fail:
	END_PROFILE(syscall_open);
	VFS_REMOVE_FSP_EXTENSION(handle, fsp);
	return -1;
}

static int
vfs_edgefs_close(struct vfs_handle_struct *handle, files_struct *fsp)
{
	struct edgefs_open_handle *oh = NULL;
	int ret;

	/* Dirrectory passed here too. */
	START_PROFILE(syscall_close);

	oh = VFS_FETCH_FSP_EXTENSION(handle, fsp);
	if (oh == NULL) {
		END_PROFILE(syscall_close);
		DBG_ERR("Failed to fetch edgefs file\n");
		return -1;
	}

	if ((oh->flags & O_DIRECTORY) && (oh->dir != NULL)) {
		ret = vfs_edgefs_closedir(handle, oh->dir);
		oh->dir = NULL;
	} else if (oh->file != NULL) {
		ret = ccow_fsio_close(oh->file);
		free(oh->full_path);
		oh->file = NULL;
	} else {
		DBG_ERR("Wrong handler passed.");
	}
	VFS_REMOVE_FSP_EXTENSION(handle, fsp);
	END_PROFILE(syscall_close);

	return ret;
}

static ssize_t
vfs_edgefs_pread(struct vfs_handle_struct *handle, files_struct *fsp,
    void *data, size_t n, off_t offset)
{
	ccow_fsio_file_t *file;
	size_t read_amount;
	ssize_t ret;
	int eof;

	START_PROFILE_BYTES(syscall_pread, n);

	file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		END_PROFILE_BYTES(syscall_pread);
		DBG_ERR("Failed to fetch edgefs file\n");
		return -1;
	}

	ret = ccow_fsio_read(file, offset, n, data, &read_amount, &eof);
	if (ret == 0) {
		ret = read_amount;
	} else {
		errno = ret;
		ret = -1;
	}
	END_PROFILE_BYTES(syscall_pread);

	return ret;
}

struct vfs_edgefs_pread_state {
	ssize_t ret;
	ccow_fsio_file_t *file;
	void *buf;
	size_t count;
	off_t offset;

	struct vfs_aio_state vfs_aio_state;
	SMBPROFILE_BYTES_ASYNC_STATE(profile_bytes);
};

static void vfs_edgefs_pread_do(void *private_data);
static void vfs_edgefs_pread_done(struct tevent_req *subreq);
static int vfs_edgefs_pread_state_destructor(struct vfs_edgefs_pread_state *state);

static struct tevent_req *
vfs_edgefs_pread_send(struct vfs_handle_struct *handle, TALLOC_CTX *mem_ctx,
    struct tevent_context *ev, files_struct *fsp, void *data, size_t n,
    off_t offset)
{
	struct vfs_edgefs_pread_state *state;
	struct tevent_req *req, *subreq;

	ccow_fsio_file_t *file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		DBG_ERR("Failed to fetch edgefs inode\n");
		return NULL;
	}

	req = tevent_req_create(mem_ctx, &state, struct vfs_edgefs_pread_state);
	if (req == NULL) {
		return NULL;
	}

	state->ret = -1;
	state->file = file;
	state->buf = data;
	state->count = n;
	state->offset = offset;

	SMBPROFILE_BYTES_ASYNC_START(syscall_asys_pread, profile_p,
			state->profile_bytes, n);
	SMBPROFILE_BYTES_ASYNC_SET_IDLE(state->profile_bytes);

	subreq = pthreadpool_tevent_job_send(
			state, ev, handle->conn->sconn->pool,
			vfs_edgefs_pread_do, state);
	if (tevent_req_nomem(subreq, req)) {
		return tevent_req_post(req, ev);
	}
	tevent_req_set_callback(subreq, vfs_edgefs_pread_done, req);

	talloc_set_destructor(state, vfs_edgefs_pread_state_destructor);

	return req;
}

static void
vfs_edgefs_pread_do(void *private_data)
{
	struct vfs_edgefs_pread_state *state = talloc_get_type_abort(
			private_data, struct vfs_edgefs_pread_state);
	struct timespec start_time;
	struct timespec end_time;
	size_t read_amount;
	int eof, ret;

	SMBPROFILE_BYTES_ASYNC_SET_BUSY(state->profile_bytes);

	PROFILE_TIMESTAMP(&start_time);

	do {
		ret = ccow_fsio_read(state->file, state->offset,
		    state->count, state->buf, &read_amount, &eof);
		if (ret == 0) {
			state->ret = read_amount;
		} else {
			state->ret = -1;
			errno = ret;
		}
	} while ((state->ret == -1) && (errno == EINTR));

	if (state->ret == -1) {
		state->vfs_aio_state.error = errno;
	}

	PROFILE_TIMESTAMP(&end_time);

	state->vfs_aio_state.duration = nsec_time_diff(&end_time, &start_time);

	SMBPROFILE_BYTES_ASYNC_SET_IDLE(state->profile_bytes);
}

static int
vfs_edgefs_pread_state_destructor(struct vfs_edgefs_pread_state *state)
{
	return -1;
}

static void
vfs_edgefs_pread_done(struct tevent_req *subreq)
{
	struct tevent_req *req = tevent_req_callback_data(
			subreq, struct tevent_req);
	struct vfs_edgefs_pread_state *state = tevent_req_data(
			req, struct vfs_edgefs_pread_state);
	int ret;

	ret = pthreadpool_tevent_job_recv(subreq);
	TALLOC_FREE(subreq);
	SMBPROFILE_BYTES_ASYNC_END(state->profile_bytes);
	talloc_set_destructor(state, NULL);
	if (ret != 0) {
		if (ret != EAGAIN) {
			tevent_req_error(req, ret);
			return;
		}
		/*
		 * If we get EAGAIN from pthreadpool_tevent_job_recv() this
		 * means the lower level pthreadpool failed to create a new
		 * thread. Fallback to sync processing in that case to allow
		 * some progress for the client.
		 */
		vfs_edgefs_pread_do(state);
	}

	tevent_req_done(req);
}

static ssize_t
vfs_edgefs_pread_recv(struct tevent_req *req,
    struct vfs_aio_state *vfs_aio_state)
{
	struct vfs_edgefs_pread_state *state = tevent_req_data(
			req, struct vfs_edgefs_pread_state);

	if (tevent_req_is_unix_error(req, &vfs_aio_state->error)) {
		return -1;
	}

	*vfs_aio_state = state->vfs_aio_state;
	return state->ret;
}

struct vfs_edgefs_pwrite_state {
	ssize_t ret;
	ccow_fsio_file_t *file;
	const void *buf;
	size_t count;
	off_t offset;

	struct vfs_aio_state vfs_aio_state;
	SMBPROFILE_BYTES_ASYNC_STATE(profile_bytes);
};

static void vfs_edgefs_pwrite_do(void *private_data);
static void vfs_edgefs_pwrite_done(struct tevent_req *subreq);
static int vfs_edgefs_pwrite_state_destructor(
    struct vfs_edgefs_pwrite_state *state);

static struct tevent_req *
vfs_edgefs_pwrite_send(struct vfs_handle_struct *handle, TALLOC_CTX *mem_ctx,
    struct tevent_context *ev, files_struct *fsp, const void *data, size_t n,
    off_t offset)
{
	struct tevent_req *req, *subreq;
	struct vfs_edgefs_pwrite_state *state;

	ccow_fsio_file_t *file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		DBG_ERR("Failed to fetch edgefs file\n");
		return NULL;
	}

	req = tevent_req_create(mem_ctx, &state, struct vfs_edgefs_pwrite_state);
	if (req == NULL) {
		return NULL;
	}

	state->ret = -1;
	state->file = file;
	state->buf = data;
	state->count = n;
	state->offset = offset;

	SMBPROFILE_BYTES_ASYNC_START(syscall_asys_pwrite, profile_p,
			state->profile_bytes, n);
	SMBPROFILE_BYTES_ASYNC_SET_IDLE(state->profile_bytes);

	subreq = pthreadpool_tevent_job_send(
			state, ev, handle->conn->sconn->pool,
			vfs_edgefs_pwrite_do, state);
	if (tevent_req_nomem(subreq, req)) {
		return tevent_req_post(req, ev);
	}
	tevent_req_set_callback(subreq, vfs_edgefs_pwrite_done, req);

	talloc_set_destructor(state, vfs_edgefs_pwrite_state_destructor);

	return req;
}

static void
vfs_edgefs_pwrite_do(void *private_data)
{
	struct vfs_edgefs_pwrite_state *state;
	struct timespec start_time;
	struct timespec end_time;
	size_t wrote;
	int ret;

	state = talloc_get_type_abort(private_data,
	    struct vfs_edgefs_pwrite_state);
	SMBPROFILE_BYTES_ASYNC_SET_BUSY(state->profile_bytes);

	PROFILE_TIMESTAMP(&start_time);

	do {
		char *buf = (char *)malloc(state->count);
		//XXX A check buf
		/* Freed by CCOW FSIO. */
		memcpy(buf, state->buf, state->count);
		ret = ccow_fsio_write(state->file, state->offset, state->count, (void *)buf, &wrote);
		if (ret == 0) {
			state->ret = wrote;
		} else {
			state->ret = -1;
			errno = ret;
		}
	} while ((state->ret == -1) && (errno == EINTR));

	if (state->ret == -1) {
		state->vfs_aio_state.error = errno;
	}

	PROFILE_TIMESTAMP(&end_time);

	state->vfs_aio_state.duration = nsec_time_diff(&end_time, &start_time);

	SMBPROFILE_BYTES_ASYNC_SET_IDLE(state->profile_bytes);
}

static int
vfs_edgefs_pwrite_state_destructor(struct vfs_edgefs_pwrite_state *state)
{
	return -1;
}

static void
vfs_edgefs_pwrite_done(struct tevent_req *subreq)
{
	struct tevent_req *req = tevent_req_callback_data(
			subreq, struct tevent_req);
	struct vfs_edgefs_pwrite_state *state = tevent_req_data(
			req, struct vfs_edgefs_pwrite_state);
	int ret;

	ret = pthreadpool_tevent_job_recv(subreq);
	TALLOC_FREE(subreq);
	SMBPROFILE_BYTES_ASYNC_END(state->profile_bytes);
	talloc_set_destructor(state, NULL);
	if (ret != 0) {
		if (ret != EAGAIN) {
			tevent_req_error(req, ret);
			return;
		}
		/*
		 * If we get EAGAIN from pthreadpool_tevent_job_recv() this
		 * means the lower level pthreadpool failed to create a new
		 * thread. Fallback to sync processing in that case to allow
		 * some progress for the client.
		 */
		vfs_edgefs_pwrite_do(state);
	}

	tevent_req_done(req);
}

static ssize_t
vfs_edgefs_pwrite_recv(struct tevent_req *req,
		struct vfs_aio_state *vfs_aio_state)
{
	struct vfs_edgefs_pwrite_state *state = tevent_req_data(
			req, struct vfs_edgefs_pwrite_state);

	if (tevent_req_is_unix_error(req, &vfs_aio_state->error)) {
		return -1;
	}

	*vfs_aio_state = state->vfs_aio_state;

	return state->ret;
}

static ssize_t
vfs_edgefs_pwrite(struct vfs_handle_struct *handle,
		files_struct *fsp, const void *data,
		size_t n, off_t offset)
{
	ssize_t ret, wrote;
	ccow_fsio_file_t *file = NULL;

	START_PROFILE_BYTES(syscall_pwrite, n);

	file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		END_PROFILE_BYTES(syscall_pwrite);
		DBG_ERR("Failed to fetch edgefs file\n");
		return -1;
	}

	ret = ccow_fsio_write(file, offset, n, (void *)data, &wrote);
	if (ret == 0) {
		ret = wrote;
	} else {
		errno = ret;
		ret = -1;
	}
	END_PROFILE_BYTES(syscall_pwrite);

	return ret;
}

static off_t
vfs_edgefs_lseek(struct vfs_handle_struct *handle,
		files_struct *fsp, off_t offset, int whence)
{
	off_t ret = 0;
DBG_INFO("%s:%d\n", __func__, __LINE__);
#if 0
	ccow_fsio_file_t *file = NULL;

	START_PROFILE(syscall_lseek);

	file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		END_PROFILE(syscall_lseek);
		DBG_ERR("Failed to fetch edgefs file\n");
		return -1;
	}

	//     ret = edgefs_lseek(file, offset, whence);
	END_PROFILE(syscall_lseek);
#endif
	return ret;
}

static ssize_t
vfs_edgefs_sendfile(struct vfs_handle_struct *handle, int tofd,
    files_struct *fromfsp, const DATA_BLOB *hdr, off_t offset, size_t n)
{
	errno = ENOTSUP;
	return -1;
}

static ssize_t
vfs_edgefs_recvfile(struct vfs_handle_struct *handle, int fromfd,
    files_struct *tofsp, off_t offset, size_t n)
{
	errno = ENOTSUP;
	return -1;
}

static int
vfs_edgefs_rename(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname_src,
    const struct smb_filename *smb_fname_dst)
{
	char *dparent_path, *sparent_path;
	char *dname, *sname;
	inode_t dparent, sparent;
	int ret;
	TALLOC_CTX *frame;
	struct smb_filename tmp;

	frame = talloc_stackframe();

	START_PROFILE(syscall_rename);
	if (!parent_dirname(frame, (const char *)smb_fname_src->base_name,
		    &sparent_path, (const char **)&sname)) {
		errno = ENOMEM;
		goto fail;
	}
	if (!parent_dirname(frame, (const char *)smb_fname_dst->base_name,
		    &dparent_path, (const char **)&dname)) {
		errno = ENOMEM;
		goto fail;
	}
	tmp.base_name = sparent_path;
	ret = vfs_edgefs_smb_fname2inode(handle, &tmp, &sparent);
	if (ret != 0) {
		goto fail;
	}
	tmp.base_name = dparent_path;
	ret = vfs_edgefs_smb_fname2inode(handle, &tmp, &dparent);
	if (ret != 0) {
		goto fail;
	}
	ret = ccow_fsio_move(HANDLE_CI(handle), sparent, sname, dparent, dname);
fail:
	TALLOC_FREE(frame);
	END_PROFILE(syscall_rename);

	return ret;
}

struct vfs_edgefs_fsync_state {
	ssize_t ret;
	ccow_fsio_file_t *file;

	struct vfs_aio_state vfs_aio_state;
	SMBPROFILE_BYTES_ASYNC_STATE(profile_bytes);
};

static void vfs_edgefs_fsync_do(void *private_data);
static void vfs_edgefs_fsync_done(struct tevent_req *subreq);
static int vfs_edgefs_fsync_state_destructor(struct vfs_edgefs_fsync_state *state);

static struct tevent_req *
vfs_edgefs_fsync_send(struct vfs_handle_struct *handle, TALLOC_CTX *mem_ctx,
    struct tevent_context *ev, files_struct *fsp)
{
	struct tevent_req *req, *subreq;
	struct vfs_edgefs_fsync_state *state;

	ccow_fsio_file_t *file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		DBG_ERR("Failed to fetch edgefs file\n");
		return NULL;
	}

	req = tevent_req_create(mem_ctx, &state, struct vfs_edgefs_fsync_state);
	if (req == NULL) {
		return NULL;
	}

	state->ret = -1;
	state->file = file;

	SMBPROFILE_BYTES_ASYNC_START(syscall_asys_fsync, profile_p,
			state->profile_bytes, 0);
	SMBPROFILE_BYTES_ASYNC_SET_IDLE(state->profile_bytes);

	subreq = pthreadpool_tevent_job_send(
	    state, ev, handle->conn->sconn->pool, vfs_edgefs_fsync_do, state);
	if (tevent_req_nomem(subreq, req)) {
		return tevent_req_post(req, ev);
	}
	tevent_req_set_callback(subreq, vfs_edgefs_fsync_done, req);

	talloc_set_destructor(state, vfs_edgefs_fsync_state_destructor);

	return req;
}

static void
vfs_edgefs_fsync_do(void *private_data)
{
	struct vfs_edgefs_fsync_state *state = talloc_get_type_abort(
			private_data, struct vfs_edgefs_fsync_state);
	struct timespec start_time;
	struct timespec end_time;
	int ret;

	SMBPROFILE_BYTES_ASYNC_SET_BUSY(state->profile_bytes);

	PROFILE_TIMESTAMP(&start_time);

	do {
		ret = ccow_fsio_flush(state->file);
		if (ret != 0) {
			state->ret = -1;
			errno = ret;
		} else {
			state->ret = 0;
		}
	} while ((state->ret == -1) && (errno == EINTR));

	if (state->ret == -1) {
		state->vfs_aio_state.error = errno;
	}

	PROFILE_TIMESTAMP(&end_time);

	state->vfs_aio_state.duration = nsec_time_diff(&end_time, &start_time);

	SMBPROFILE_BYTES_ASYNC_SET_IDLE(state->profile_bytes);
}

static int
vfs_edgefs_fsync_state_destructor(struct vfs_edgefs_fsync_state *state)
{
	return -1;
}

static void
vfs_edgefs_fsync_done(struct tevent_req *subreq)
{
	struct tevent_req *req = tevent_req_callback_data(
			subreq, struct tevent_req);
	struct vfs_edgefs_fsync_state *state = tevent_req_data(
			req, struct vfs_edgefs_fsync_state);
	int ret;

	ret = pthreadpool_tevent_job_recv(subreq);
	TALLOC_FREE(subreq);
	SMBPROFILE_BYTES_ASYNC_END(state->profile_bytes);
	talloc_set_destructor(state, NULL);
	if (ret != 0) {
		if (ret != EAGAIN) {
			tevent_req_error(req, ret);
			return;
		}
		/*
		 * If we get EAGAIN from pthreadpool_tevent_job_recv() this
		 * means the lower level pthreadpool failed to create a new
		 * thread. Fallback to sync processing in that case to allow
		 * some progress for the client.
		 */
		vfs_edgefs_fsync_do(state);
	}

	tevent_req_done(req);
}

static int
vfs_edgefs_fsync_recv(struct tevent_req *req,
    struct vfs_aio_state *vfs_aio_state)
{
	struct vfs_edgefs_fsync_state *state = tevent_req_data(
			req, struct vfs_edgefs_fsync_state);

	if (tevent_req_is_unix_error(req, &vfs_aio_state->error)) {
		return -1;
	}

	*vfs_aio_state = state->vfs_aio_state;
	return state->ret;
}

static int
vfs_edgefs_stat(struct vfs_handle_struct *handle,
    struct smb_filename *smb_fname)
{
	struct stat st;
	inode_t inode;
	int ret;

	ret = vfs_edgefs_smb_fname2inode(handle, smb_fname, &inode);
	if (ret != 0) {
		if (ret != ENOENT)
			DBG_ERR("Failed to fetch edgefs inode (ERROR: %s)\n",
			    strerror(ret));
		return ENOENT;
	}

	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), inode, &st);
	if (ret == 0) {
		smb_stat_ex_from_stat(&smb_fname->st, &st);
	}
	if (ret < 0) {
		DEBUG(0, ("edgefs_fstat(%s) failed: %s\n",
		    smb_fname->base_name, strerror(errno)));
	}
	END_PROFILE(syscall_fstat);

	return ret;
}

static int
vfs_edgefs_fstat(vfs_handle_struct *handle, files_struct *fsp,
    SMB_STRUCT_STAT *sbuf)
{
	struct vfs_edgefs_dir *dir;
	ccow_fsio_file_t *file;
	struct stat st;
	inode_t ino;
	int ret;

	DEBUG(10, ("Entering with fsp->fsp_name->base_name "
		   "'%s'\n", fsp_str_dbg(fsp)));

	file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		dir = vfs_edgefs_fetch_dir(handle, fsp);
		if (dir == NULL) {
			END_PROFILE(syscall_fchmod);
			DBG_ERR("Failed to fetch edgefs file\n");
			return -1;
		} else
			ino = dir->dir_ino;
	} else
		ino = file->ino;

	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), ino, &st);
	if (ret == 0) {
		smb_stat_ex_from_stat(sbuf, &st);
	} else {
		errno = ret;
		ret = -1;
	}

	return ret;
}

static int
vfs_edgefs_lstat(struct vfs_handle_struct *handle,
    struct smb_filename *smb_fname)
{
	return vfs_edgefs_stat(handle, smb_fname); //XXX Resolve links here
}

static uint64_t
vfs_edgefs_get_alloc_size(struct vfs_handle_struct *handle, files_struct *fsp,
    const SMB_STRUCT_STAT *sbuf)
{
DBG_INFO("%s:%d\n", __func__, __LINE__);
	uint64_t ret;

	START_PROFILE(syscall_get_alloc_size);
	//XXX
	ret = sbuf->st_ex_blocks * 512;
	END_PROFILE(syscall_get_alloc_size);

	return ret;
}

static int
vfs_edgefs_chmod(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, mode_t mode)
{
	struct stat stat;
	inode_t inode;
	int ret;

	ret = ccow_fsio_find(HANDLE_CI(handle), smb_fname->base_name, &inode);
	if (ret != 0) {
		DBG_ERR("Failed to fetch edgefs inode (ERROR: %s)\n",
		    strerror(ret));
		return ENOENT;
	}

	START_PROFILE(syscall_chmod);
	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), inode, &stat);
	if (ret != 0) {
		errno = ret;
		return (-1);
	}

	stat.st_mode = mode;
	ret = ccow_fsio_set_file_stat(HANDLE_CI(handle), inode, &stat);
	if (ret != 0) {
		errno = ret;
		return (-1);
	}
	END_PROFILE(syscall_chmod);

	return ret;
}

static int
vfs_edgefs_fchmod(struct vfs_handle_struct *handle, files_struct *fsp,
    mode_t mode)
{
	int ret;
	struct stat stat;
	ccow_fsio_file_t *file = NULL;

	START_PROFILE(syscall_fchmod);

	file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		END_PROFILE(syscall_fchmod);
		DBG_ERR("Failed to fetch edgefs file\n");
		return -1;
	}

	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), file->ino, &stat);
	if (ret != 0) {
		errno = ret;
		return (-1);
	}
	stat.st_mode = mode;
	ret = ccow_fsio_set_file_stat(HANDLE_CI(handle), file->ino, &stat);
	if (ret != 0) {
		errno = ret;
		return (-1);
	}
	END_PROFILE(syscall_fchmod);

	return ret;
}

static int
vfs_edgefs_chown(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, uid_t uid, gid_t gid)
{
	struct stat stat;
	inode_t inode;
	int ret;

	ret = ccow_fsio_find(HANDLE_CI(handle), smb_fname->base_name, &inode);
	if (ret != 0) {
		DBG_ERR("Failed to fetch edgefs inode (ERROR: %s)\n",
		    strerror(ret));
		return ENOENT;
	}

	START_PROFILE(syscall_chown);
	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), inode, &stat);
	stat.st_uid = uid;
	stat.st_gid = gid;
	ret = ccow_fsio_set_file_stat(HANDLE_CI(handle), inode, &stat);
	END_PROFILE(syscall_chown);

	return ret;
}

static int
vfs_edgefs_fchown(struct vfs_handle_struct *handle, files_struct *fsp,
    uid_t uid, gid_t gid)
{
	ccow_fsio_file_t *file = NULL;
	struct stat stat;
	int ret;

	START_PROFILE(syscall_fchown);

	file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		END_PROFILE(syscall_fchown);
		DBG_ERR("Failed to fetch edgefs file\n");
		return -1;
	}

	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), file->ino, &stat);
	stat.st_uid = uid;
	stat.st_gid = gid;
	ret = ccow_fsio_set_file_stat(HANDLE_CI(handle), file->ino, &stat);
	END_PROFILE(syscall_fchown);

	return ret;
}

static int
vfs_edgefs_lchown(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, uid_t uid, gid_t gid)
{
DBG_INFO("%s:%d\n", __func__, __LINE__);
	int ret;

	ret = 0;
	START_PROFILE(syscall_lchown);
	//     ret = edgefs_lchown(HANDLE_CI(handle), smb_fname->base_name, uid, gid);
	END_PROFILE(syscall_lchown);

	return ret;
}

static int
vfs_edgefs_chdir(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname)
{
	char *newpath;
	int ret;

	if (smb_fname->base_name[0] == '/') {
		newpath = strdup(smb_fname->base_name);
		if (newpath == NULL)
			return (errno);
	} else {
		ret = asprintf(&newpath, "%s/%s", handle->conn->cwd_fname->base_name,
		    smb_fname->base_name);
		if (ret == -1)
			return (errno);
	}
	free(HANDLE_CWD(handle));
	HANDLE_CWD(handle) = newpath;
	return (0);
}

static struct smb_filename *
vfs_edgefs_getwd(struct vfs_handle_struct *handle, TALLOC_CTX *ctx)
{
	struct smb_filename *result;

	result = synthetic_smb_fname(ctx,
					HANDLE_CWD(handle),
					NULL,
					NULL,
					0);

	return (result);
}

static int
vfs_edgefs_ntimes(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, struct smb_file_time *ft)
{
	int ret = -1;
	struct stat stat;
	inode_t inode;
	char *name, *path;

	START_PROFILE(syscall_ntimes);

	name = smb_fname->base_name;
	if (name[0] == '/') {
		path = strdup(name); // XXX A
		if (path == NULL)
			return (errno);
	} else {
		ret = asprintf(&path, "%s/%s", handle->conn->cwd_fname->base_name,
		    name);
		if (ret == -1)
			return (errno);
	}
	if (strlen(path) > 0 && path[strlen(path) - 1] == '.')
		path[strlen(path) - 1] = '\0';
	name = path;
	if (strstr(name, handle->conn->connectpath) != name) {
		free(path);
		return SMB_VFS_NEXT_NTIMES(handle, smb_fname, ft);
	} else {
		name += strlen(handle->conn->connectpath);
	}


	ret = ccow_fsio_find(HANDLE_CI(handle), name, &inode);
	if (ret != 0) {
		errno = ret;
		ret = -1;
		goto fail;
	}


	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), inode, &stat);
	if (ret != 0) {
		errno = ret;
		ret = -1;
		goto fail;
	}

	if (null_timespec(ft->atime)) {
		stat.st_atim.tv_sec = smb_fname->st.st_ex_atime.tv_sec;
		stat.st_atim.tv_nsec = smb_fname->st.st_ex_atime.tv_nsec;
	} else {
		stat.st_atim.tv_sec = ft->atime.tv_sec;
		stat.st_atim.tv_nsec = ft->atime.tv_nsec;
	}

	if (null_timespec(ft->mtime)) {
		stat.st_mtim.tv_sec = smb_fname->st.st_ex_mtime.tv_sec;
		stat.st_mtim.tv_nsec = smb_fname->st.st_ex_mtime.tv_nsec;
	} else {
		stat.st_mtim.tv_sec = ft->mtime.tv_sec;
		stat.st_mtim.tv_nsec = ft->mtime.tv_nsec;
	}

	if ((timespec_compare(&stat.st_atim,
			    &smb_fname->st.st_ex_atime) == 0) &&
	    (timespec_compare(&stat.st_mtim,
			      &smb_fname->st.st_ex_mtime) == 0)) {
		ret = 0;
		goto success;
	}

	ret = ccow_fsio_set_file_stat(HANDLE_CI(handle), inode, &stat);
	if (ret != 0) {
		errno = ret;
		ret = -1;
	}
fail:
	END_PROFILE(syscall_ntimes);
success:
	free(path);
	return ret;
}

static int
vfs_edgefs_ftruncate(struct vfs_handle_struct *handle, files_struct *fsp,
    off_t offset)
{
	ccow_fsio_file_t *file = NULL;
	struct stat stat;
	int ret;

	START_PROFILE(syscall_ftruncate);

	file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		END_PROFILE(syscall_ftruncate);
		DBG_ERR("Failed to fetch edgefs file\n");
		return -1;
	}

	ret = ccow_fsio_get_file_stat(HANDLE_CI(handle), file->ino, &stat);
	stat.st_size = 0;
	ret = ccow_fsio_set_file_stat(HANDLE_CI(handle), file->ino, &stat);
	END_PROFILE(syscall_ftruncate);

	if (ret != 0) {
		errno = ret;
		ret = -1;
	}
	return (ret);
}

static int
vfs_edgefs_fallocate(struct vfs_handle_struct *handle,
    struct files_struct *fsp, uint32_t mode, off_t offset, off_t len)
{
DBG_INFO("%s:%d\n", __func__, __LINE__);
	errno = ENOTSUP;
	return -1;
}

static struct smb_filename *
vfs_edgefs_realpath(struct vfs_handle_struct *handle, TALLOC_CTX *ctx,
    const struct smb_filename *smb_fname)
{
	char *result = NULL;
	const char *path = smb_fname->base_name;
	size_t len = strlen(path);
	struct smb_filename *result_fname = NULL;
	int r = -1;

	if (len && (path[0] == '/')) {
		r = asprintf(&result, "%s", path); // XXX A
	} else if ((len >= 2) && (path[0] == '.') && (path[1] == '/')) {
		if (len == 2) {
			r = asprintf(&result, "%s",
			    handle->conn->cwd_fname->base_name);
		} else {
			r = asprintf(&result, "%s/%s", HANDLE_CWD(handle),
			    &path[2]);
		}
	} else {
		r = asprintf(&result, "%s/%s", HANDLE_CWD(handle), path);
	}

	if (r == -1) {
		return NULL;
	}

	result_fname = synthetic_smb_fname(ctx, result, NULL, NULL, 0);
	SAFE_FREE(result);
	return result_fname;
}

static bool
vfs_edgefs_lock(struct vfs_handle_struct *handle, files_struct *fsp, int op,
    off_t offset, off_t count, int type)
{
	DBG_INFO("%d op: %d, offset: %lu, count: %lu, type: %d\n", __LINE__,
	    op, offset, count, type);
	struct flock flock = { 0, };
	int ret;
	ccow_fsio_file_t *file = NULL;
	bool ok = false;

	START_PROFILE(syscall_fcntl_lock);

	file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		DBG_ERR("Failed to fetch edgefs file\n");
		ok = false;
		goto out;
	}

	if (op == F_GETLK)
		ret = ccow_fsio_query_lock(HANDLE_CI(handle), file->ino, type,
		    offset, count, &flock);
	else
		ret = ccow_fsio_lock(HANDLE_CI(handle), file->ino, type, offset,
		    count);

	DBG_INFO("%d ino: %lu, op: %d, offset: %lu, count: %lu, type: %d. "
	    "Returned: %d\n", __LINE__, file->ino, op, offset, count, type,
	    ret);

	if (op == F_GETLK) {
		/* lock query, true if someone else has locked */
		if ((ret == 0) &&
		    (flock.l_type != F_UNLCK) &&
		    (flock.l_pid != 0) && (flock.l_pid != getpid())) {
			ok = true;
			goto out;
		}
		/* not me */
		ok = false;
		errno = ret;
		goto out;
	}

	if (ret != 0) {
		ok = false;
		errno = ret;
		goto out;
	}

	ok = true;
out:
	END_PROFILE(syscall_fcntl_lock);

	return ok;
}

static int
vfs_edgefs_kernel_flock(struct vfs_handle_struct *handle, files_struct *fsp,
    uint32_t share_mode, uint32_t access_mask)
{

	errno = ENOSYS;
	return -1;
}

static int
vfs_edgefs_linux_setlease(struct vfs_handle_struct *handle, files_struct *fsp,
    int leasetype)
{

	errno = ENOSYS;
	return -1;
}

static bool
vfs_edgefs_getlock(struct vfs_handle_struct *handle, files_struct *fsp,
    off_t *poffset, off_t *pcount, int *ptype, pid_t *ppid)
{
	struct flock flock = { 0, };
	int ret;
	ccow_fsio_file_t *file = NULL;

	START_PROFILE(syscall_fcntl_getlock);

	file = vfs_edgefs_fetch_file(handle, fsp);
	if (file == NULL) {
		END_PROFILE(syscall_fcntl_getlock);
		DBG_ERR("Failed to fetch edgefs file\n");
		return false;
	}

	ret = ccow_fsio_query_lock(HANDLE_CI(handle), file->ino, *ptype,
	    *poffset, *pcount, &flock);

	if (ret != 0) {
		END_PROFILE(syscall_fcntl_getlock);
		errno = ret;
		return false;
	}

	*ptype = flock.l_type;
	*poffset = flock.l_start;
	*pcount = flock.l_len;
	*ppid = flock.l_pid;
	END_PROFILE(syscall_fcntl_getlock);
	return true;
}

static int
vfs_edgefs_symlink(struct vfs_handle_struct *handle, const char *link_target,
    const struct smb_filename *new_smb_fname)
{
	char *parent_path, *name;
	TALLOC_CTX *frame;
	inode_t inode, parent;
	int mode, uid, gid, ret;

	frame = talloc_stackframe();
	mode = 0644; // XXX
	uid = gid = 0;

	START_PROFILE(syscall_symlink);
	if (!parent_dirname(frame, (const char *)new_smb_fname->base_name,
		    &parent_path, (const char **)&name)) {
		errno = ENOMEM;
		goto fail;
	}
	// XXX wrong path
	ret = ccow_fsio_find(HANDLE_CI(handle), parent_path, &parent);
	if (ret != 0) {
		goto fail;
	}
	ret = ccow_fsio_mksymlink(HANDLE_CI(handle), parent, name, mode,
	    uid, gid, &inode, (char *)link_target);
fail:
	TALLOC_FREE(frame);
	END_PROFILE(syscall_symlink);

	return ret;
}

static int
vfs_edgefs_readlink(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, char *buf, size_t bufsiz)
{
	char *target;
	inode_t inode;
	int ret;

	START_PROFILE(syscall_readlink);
	// XXX wrong path
	ret = ccow_fsio_find(HANDLE_CI(handle), smb_fname->base_name, &inode);
	if (ret != 0) {
		goto fail;
	}
	ret = ccow_fsio_readsymlink(HANDLE_CI(handle), inode, &target);
	if (ret != 0) {
		errno = ret;
		ret = -1;
	}
fail:
	END_PROFILE(syscall_readlink);

	return ret;
}

static int
vfs_edgefs_link(struct vfs_handle_struct *handle,
    const struct smb_filename *old_smb_fname,
    const struct smb_filename *new_smb_fname)
{
	char *newparent_path, *newname;
	TALLOC_CTX *frame;
	inode_t oldinode, newparent;
	int ret;

	frame = talloc_stackframe();

	START_PROFILE(syscall_link);
	if (!parent_dirname(frame, (const char *)new_smb_fname->base_name,
		    &newparent_path, (const char **)&newname)) {
		errno = ENOMEM;
		goto fail;
	}
	// XXX wrong path
	ret = ccow_fsio_find(HANDLE_CI(handle), newparent_path, &newparent);
	if (ret != 0) {
		goto fail;
	}
	// XXX wrong path
	ret = ccow_fsio_find(HANDLE_CI(handle), old_smb_fname->base_name, &oldinode);
	if (ret != 0) {
		goto fail;
	}
	ret = ccow_fsio_link(HANDLE_CI(handle), newparent, new_smb_fname->base_name,
	    oldinode);
	if (ret != 0) {
		errno = ret;
		ret = -1;
	}
fail:
	TALLOC_FREE(frame);
	END_PROFILE(syscall_link);

	return ret;
}

static int
vfs_edgefs_mknod(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, mode_t mode, SMB_DEV_T dev)
{
	errno = ENOSYS;
	return -1;
}

static int
vfs_edgefs_chflags(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname, unsigned int flags)
{

	errno = ENOSYS;
	return -1;
}

static int
vfs_edgefs_get_real_filename(struct vfs_handle_struct *handle,
    const char *path, const char *name, TALLOC_CTX *mem_ctx, char **found_name)
{

	errno = EOPNOTSUPP;
	return -1;
}

static const char *
vfs_edgefs_connectpath(struct vfs_handle_struct *handle,
    const struct smb_filename *smb_fname)
{

	DBG_INFO("%d handle->conn->connectpath = \"%s\"\n", __LINE__,
	    handle->conn->connectpath);
	return handle->conn->connectpath;
}


/* AIO Operations */

static bool
vfs_edgefs_aio_force(struct vfs_handle_struct *handle, files_struct *fsp)
{

	return false;
}

static struct vfs_fn_pointers edgefs_fns = {

	/* Disk Operations */

	.connect_fn = vfs_edgefs_connect,
	.disconnect_fn = vfs_edgefs_disconnect,
	.disk_free_fn = vfs_edgefs_disk_free,
	.get_quota_fn = vfs_edgefs_get_quota,
	.set_quota_fn = vfs_edgefs_set_quota,
	.statvfs_fn = vfs_edgefs_statvfs,
	.fs_capabilities_fn = vfs_edgefs_fs_capabilities,

	.get_dfs_referrals_fn = NULL,

	/* Directory Operations */

	.opendir_fn = vfs_edgefs_opendir,
	.fdopendir_fn = vfs_edgefs_fdopendir,
	.readdir_fn = vfs_edgefs_readdir,
	.seekdir_fn = vfs_edgefs_seekdir,
	.telldir_fn = vfs_edgefs_telldir,
	.rewind_dir_fn = vfs_edgefs_rewinddir,
	.mkdir_fn = vfs_edgefs_mkdir,
	.rmdir_fn = vfs_edgefs_unlink,
	.closedir_fn = vfs_edgefs_closedir,

	/* File Operations */

	.open_fn = vfs_edgefs_open,
	.create_file_fn = NULL,
	.close_fn = vfs_edgefs_close,
	.pread_fn = vfs_edgefs_pread,
	.pread_send_fn = vfs_edgefs_pread_send,
	.pread_recv_fn = vfs_edgefs_pread_recv,
	.pwrite_fn = vfs_edgefs_pwrite,
	.pwrite_send_fn = vfs_edgefs_pwrite_send,
	.pwrite_recv_fn = vfs_edgefs_pwrite_recv,
	.lseek_fn = vfs_edgefs_lseek,
	.sendfile_fn = vfs_edgefs_sendfile,
	.recvfile_fn = vfs_edgefs_recvfile,
	.rename_fn = vfs_edgefs_rename,
	.fsync_send_fn = vfs_edgefs_fsync_send,
	.fsync_recv_fn = vfs_edgefs_fsync_recv,

	.stat_fn = vfs_edgefs_stat,
	.fstat_fn = vfs_edgefs_fstat,
	.lstat_fn = vfs_edgefs_lstat,
	.get_alloc_size_fn = vfs_edgefs_get_alloc_size,
	.unlink_fn = vfs_edgefs_unlink,

	.chmod_fn = vfs_edgefs_chmod,
	.fchmod_fn = vfs_edgefs_fchmod,
	.chown_fn = vfs_edgefs_chown,
	.fchown_fn = vfs_edgefs_fchown,
	.lchown_fn = vfs_edgefs_lchown,
	.chdir_fn = vfs_edgefs_chdir,
	.getwd_fn = vfs_edgefs_getwd,
	.ntimes_fn = vfs_edgefs_ntimes,
	.ftruncate_fn = vfs_edgefs_ftruncate,
	.fallocate_fn = vfs_edgefs_fallocate,
	.lock_fn = vfs_edgefs_lock,
#if 0
	.kernel_flock_fn = vfs_edgefs_kernel_flock,
#endif
	.linux_setlease_fn = vfs_edgefs_linux_setlease,
	.getlock_fn = vfs_edgefs_getlock,
	.symlink_fn = vfs_edgefs_symlink,
	.readlink_fn = vfs_edgefs_readlink,
	.link_fn = vfs_edgefs_link,
	.mknod_fn = vfs_edgefs_mknod,
	.realpath_fn = vfs_edgefs_realpath,
	.chflags_fn = vfs_edgefs_chflags,
	.file_id_create_fn = NULL,
	.streaminfo_fn = NULL,
	.get_real_filename_fn = vfs_edgefs_get_real_filename,
	.connectpath_fn = vfs_edgefs_connectpath,

	.brl_lock_windows_fn = NULL,
	.brl_unlock_windows_fn = NULL,
	.strict_lock_check_fn = NULL,
	.translate_name_fn = NULL,
	.fsctl_fn = NULL,

	/* NT ACL Operations */
	.fget_nt_acl_fn = NULL,
	.get_nt_acl_fn = NULL,
	.fset_nt_acl_fn = NULL,
	.audit_file_fn = NULL,

	/* Posix ACL Operations */
	//.sys_acl_get_file_fn = posixacl_xattr_acl_get_file,
	//.sys_acl_get_fd_fn = posixacl_xattr_acl_get_fd,
	//.sys_acl_blob_get_file_fn = posix_sys_acl_blob_get_file,
	//.sys_acl_blob_get_fd_fn = posix_sys_acl_blob_get_fd,
	//.sys_acl_set_file_fn = posixacl_xattr_acl_set_file,
	//.sys_acl_set_fd_fn = posixacl_xattr_acl_set_fd,
	//.sys_acl_delete_def_file_fn = posixacl_xattr_acl_delete_def_file,
#if 1
	/* EA Operations */
	.getxattr_fn = vfs_not_implemented_getxattr,
	.getxattrat_send_fn = vfs_not_implemented_getxattrat_send,
	.getxattrat_recv_fn = vfs_not_implemented_getxattrat_recv,
	.fgetxattr_fn = vfs_not_implemented_fgetxattr,
	.listxattr_fn = vfs_not_implemented_listxattr,
	.flistxattr_fn = vfs_not_implemented_flistxattr,
	.removexattr_fn = vfs_not_implemented_removexattr,
	.fremovexattr_fn = vfs_not_implemented_fremovexattr,
	.setxattr_fn = vfs_not_implemented_setxattr,
	.fsetxattr_fn = vfs_not_implemented_fsetxattr,
#endif
	/* AIO Operations */
	.aio_force_fn = vfs_edgefs_aio_force,

	/* Durable handle Operations */
	.durable_cookie_fn = NULL,
	.durable_disconnect_fn = NULL,
	.durable_reconnect_fn = NULL,
};

static_decl_vfs;
NTSTATUS
vfs_edgefs_init(TALLOC_CTX *ctx)
{

	ccow_fsio_init();

	return smb_register_vfs(SMB_VFS_INTERFACE_VERSION,
			"edgefs", &edgefs_fns);
}
