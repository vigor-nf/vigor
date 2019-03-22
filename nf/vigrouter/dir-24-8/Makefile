CFLAGS = -std=c11
CFLAGS += -Wall -g

all: tests

tests: tests.o dir-24-8-basic.o indexmap.o

tests.o: tests.c dir-24-8-basic.h indexmap.h

dir-24-8-basic.o: dir-24-8-basic.c dir-24-8-basic.h indexmap.h

indexmap.o: indexmap.c indexmap.h
