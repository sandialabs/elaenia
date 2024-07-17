
CC = gcc-mp-11

overflow: overflow.c
	$(CC) -o $@ $< -ggdb -O3 -Wall -fstack-protector-all -Wno-error=format-security -fstack-protector-all -lm -lpthread

#-warn-special-float nan
frama-c: overflow.c
	frama-c -eva -main fc_main -eva-use-spec checkOverflow *.c >log

clean:
	$(RM) *.o sqrt

