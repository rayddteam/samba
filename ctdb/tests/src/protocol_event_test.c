/*
   protocol types tests

   Copyright (C) Amitay Isaacs  2015

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, see <http://www.gnu.org/licenses/>.
*/

#include <assert.h>

#include "protocol/protocol_basic.c"
#include "protocol/protocol_types.c"
#include "protocol/protocol_event.c"

#include "tests/src/protocol_common.h"
#include "tests/src/protocol_common_event.h"

#define REQID		0x34567890


/*
 * Functions to test eventd protocol marshalling
 */

static void test_ctdb_event_header(void)
{
	TALLOC_CTX *mem_ctx;
	size_t buflen;
	struct ctdb_event_header h, h2;
	int ret;

	printf("ctdb_event_header\n");
	fflush(stdout);

	mem_ctx = talloc_new(NULL);
	assert(mem_ctx != NULL);

	ctdb_event_header_fill(&h, REQID);

	buflen = ctdb_event_header_len(&h);
	ctdb_event_header_push(&h, BUFFER);
	ret = ctdb_event_header_pull(BUFFER, buflen, mem_ctx, &h2);
	assert(ret == 0);

	verify_ctdb_event_header(&h, &h2);

	talloc_free(mem_ctx);
}

#define NUM_COMMANDS	5

static void test_ctdb_event_request_data(void)
{
	TALLOC_CTX *mem_ctx;
	size_t buflen;
	struct ctdb_event_request_data rd, rd2;
	uint32_t command;
	int ret;

	printf("ctdb_event_request_data\n");
	fflush(stdout);

	for (command=1; command<=NUM_COMMANDS; command++) {
		mem_ctx = talloc_new(NULL);
		assert(mem_ctx != NULL);

		printf("%u.. ", command);
		fflush(stdout);
		fill_ctdb_event_request_data(mem_ctx, &rd, command);
		buflen = ctdb_event_request_data_len(&rd);
		ctdb_event_request_data_push(&rd, BUFFER);
		ret = ctdb_event_request_data_pull(BUFFER, buflen, mem_ctx, &rd2);
		assert(ret == 0);
		verify_ctdb_event_request_data(&rd, &rd2);

		talloc_free(mem_ctx);
	}

	printf("\n");
	fflush(stdout);
}

static void test_ctdb_event_reply_data(void)
{
	TALLOC_CTX *mem_ctx;
	size_t buflen;
	struct ctdb_event_reply_data rd, rd2;
	uint32_t command;
	int ret;

	printf("ctdb_event_reply_data\n");
	fflush(stdout);

	for (command=1; command<=NUM_COMMANDS; command++) {
		mem_ctx = talloc_new(NULL);
		assert(mem_ctx != NULL);

		printf("%u.. ", command);
		fflush(stdout);
		fill_ctdb_event_reply_data(mem_ctx, &rd, command);
		buflen = ctdb_event_reply_data_len(&rd);
		ctdb_event_reply_data_push(&rd, BUFFER);
		ret = ctdb_event_reply_data_pull(BUFFER, buflen, mem_ctx, &rd2);
		assert(ret == 0);
		verify_ctdb_event_reply_data(&rd, &rd2);

		talloc_free(mem_ctx);
	}

	printf("\n");
	fflush(stdout);
}

static void test_ctdb_event_request(void)
{
	TALLOC_CTX *mem_ctx;
	uint8_t *buf;
	size_t len, buflen;
	int ret;
	struct ctdb_event_request r, r2;
	uint32_t command;

	printf("ctdb_event_request\n");
	fflush(stdout);

	for (command=1; command<=NUM_COMMANDS; command++) {
		mem_ctx = talloc_new(NULL);
		assert(mem_ctx != NULL);

		printf("%u.. ", command);
		fflush(stdout);
		fill_ctdb_event_request(mem_ctx, &r, command);
		buflen = ctdb_event_request_len(&r);
		buf = talloc_size(mem_ctx, buflen);
		assert(buf != NULL);
		len = 0;
		ret = ctdb_event_request_push(&r, buf, &len);
		assert(ret == EMSGSIZE);
		assert(len == buflen);
		ret = ctdb_event_request_push(&r, buf, &buflen);
		assert(ret == 0);
		ret = ctdb_event_request_pull(buf, buflen, mem_ctx, &r2);
		assert(ret == 0);
		assert(r2.header.length == buflen);
		verify_ctdb_event_request(&r, &r2);

		talloc_free(mem_ctx);
	}

	printf("\n");
	fflush(stdout);
}

static void test_ctdb_event_reply(void)
{
	TALLOC_CTX *mem_ctx;
	uint8_t *buf;
	size_t len, buflen;
	int ret;
	struct ctdb_event_reply r, r2;
	uint32_t command;

	printf("ctdb_event_reply\n");
	fflush(stdout);

	for (command=1; command<=NUM_COMMANDS; command++) {
		mem_ctx = talloc_new(NULL);
		assert(mem_ctx != NULL);

		printf("%u.. ", command);
		fflush(stdout);
		fill_ctdb_event_reply(mem_ctx, &r, command);
		buflen = ctdb_event_reply_len(&r);
		buf = talloc_size(mem_ctx, buflen);
		assert(buf != NULL);
		len = 0;
		ret = ctdb_event_reply_push(&r, buf, &len);
		assert(ret == EMSGSIZE);
		assert(len == buflen);
		ret = ctdb_event_reply_push(&r, buf, &buflen);
		assert(ret == 0);
		ret = ctdb_event_reply_pull(buf, buflen, mem_ctx, &r2);
		assert(ret == 0);
		assert(r2.header.length == buflen);
		verify_ctdb_event_reply(&r, &r2);

		talloc_free(mem_ctx);
	}

	printf("\n");
	fflush(stdout);
}

DEFINE_TEST(struct ctdb_event_request_run, ctdb_event_request_run);
DEFINE_TEST(struct ctdb_event_request_status, ctdb_event_request_status);
DEFINE_TEST(struct ctdb_event_request_script_enable,
				ctdb_event_request_script_enable);
DEFINE_TEST(struct ctdb_event_request_script_disable,
				ctdb_event_request_script_disable);
DEFINE_TEST(struct ctdb_event_reply_status, ctdb_event_reply_status);
DEFINE_TEST(struct ctdb_event_reply_script_list, ctdb_event_reply_script_list);

int main(int argc, char *argv[])
{
	if (argc == 2) {
		int seed = atoi(argv[1]);
		srandom(seed);
	}

	TEST_FUNC(ctdb_event_request_run)();
	TEST_FUNC(ctdb_event_request_status)();
	TEST_FUNC(ctdb_event_request_script_enable)();
	TEST_FUNC(ctdb_event_request_script_disable)();
	TEST_FUNC(ctdb_event_reply_status)();
	TEST_FUNC(ctdb_event_reply_script_list)();

	test_ctdb_event_header();

	test_ctdb_event_request_data();
	test_ctdb_event_reply_data();
	test_ctdb_event_request();
	test_ctdb_event_reply();

	return 0;
}