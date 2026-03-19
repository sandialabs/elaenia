
CC = gcc

sqrt: sqrt.c
	$(CC) -c -o sqrt.o sqrt.c -ggdb -O3 -Wall -fstack-protector-all -Wno-error=format-security -fstack-protector-all -lm -lpthread
	$(CC) -o sqrt sqrt.o


frama-c: sqrt.c
	frama-c -eva *.c

clean:
	$(RM) *.o sqrt

