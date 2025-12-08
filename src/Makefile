CC=gcc
CFLAGS=-Wall -Wextra -pedantic

all: main

main: common.h lst.h graphs.h const_space.h mem.h proj.c
	$(CC) $(CFLAGS) -o main proj.c

clean:
	rm -rf ./main
