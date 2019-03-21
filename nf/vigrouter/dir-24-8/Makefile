CFLAGS = -std=c11
CFLAGS += -Wall -g

all: tests

tests: tests.o dir-24-8-basic.o bitmap.o

tests.o: tests.c dir-24-8-basic.h bitmap.h

dir-24-8-basic.o: dir-24-8-basic.c dir-24-8-basic.h bitmap.h

bitmap.o: bitmap.c bitmap.h
