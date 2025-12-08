CC=gcc
CFLAGS=-Wall -Wextra -pedantic

all: main

main: list_shape.h lst.h mem.h proj.c
	$(CC) $(CFLAGS) -o main proj.c

clean:
	rm -rf ./main
