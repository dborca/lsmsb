/*
 *  Tool for running programs under a given sandbox (CONFIG_SECURITY_LSMSB)
 *
 *  Copyright (c) 2010 dborca
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 */


#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>


#define CHECK_SB '+'


#ifdef CHECK_SB
#define ATTR_MODE O_RDWR
#else
#define ATTR_MODE O_RDONLY
#endif


int
main(int argc, char **argv)
{
    int rv;
    int fd;
    struct stat st;
    uint8_t *buffer, ch;
    const char *myself = argv[0];

    if (argc < 2) {
	printf("%s: missing operand\n", myself);
	goto err1;
    }

    if (!strcmp(argv[1], "--help")) {
	printf("usage: %s sandbox [COMMAND [ARG]...]\n", myself);
	return 0;
    }

    fd = open(argv[1], O_RDONLY);
    if (fd < 0) {
	perror(argv[1]);
	goto err1;
    }

    rv = fstat(fd, &st);
    if (rv < 0) {
	perror(argv[1]);
	goto err2;
    }

    buffer = malloc(st.st_size);
    if (!buffer) {
	perror("buffer");
	goto err2;
    }

    if (read(fd, buffer, st.st_size) != st.st_size) {
	perror("read");
	goto err3;
    }

    rv = open("/proc/self/attr/current", ATTR_MODE);
    if (rv < 0) {
	perror("/proc/self/attr/current");
	goto err3;
    }

    close(fd);
    fd = rv;

#ifdef CHECK_SB
    if (read(fd, &ch, 1) != 1) {
	perror("lsmsb");
	goto err3;
    }

    if (ch != CHECK_SB) {
	fprintf(stderr, "lsmsb: not available\n");
	goto err3;
    }

    rv = lseek(fd, 0, SEEK_SET);
    if (rv) {
	perror("lsmsb");
	goto err3;
    }
#endif

    if (write(fd, buffer, st.st_size) != st.st_size) {
	perror("write");
	goto err3;
    }

    free(buffer);
    close(fd);

    if (seteuid(getuid()) || setegid(getgid())) {
	goto err1;
    }

    fprintf(stderr, "Sandbox installed\n");

    if (argc <= 2) {
	rv = execl("/bin/sh", "/bin/sh", NULL);
    } else {
	argv += 2;
	rv = execvp(argv[0], argv);
    }

    return rv;

  err3:
    free(buffer);
  err2:
    close(fd);
  err1:
    return 127;
}
