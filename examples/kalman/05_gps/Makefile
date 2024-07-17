CFLAGS = -g -Wall

HEADERS = Matrix_Algebra.h

gps: gps.o Matrix_Algebra.o
	$(CC) $(CFLAGS) -o $@ $^

gps.o: gps.c Matrix_Algebra.o $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $<

Matrix_Algebra.o: Matrix_Algebra.c $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $<

.PHONY: clean

clean:
	$(RM) gps *.o
