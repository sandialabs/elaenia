CC = clang
CFLAGS = -g -Wall

HEADERS = Matrix_Algebra.h

TESTBEDS = driver_33 driver_mn

all: $(TESTBEDS)

driver_33: driver_33.o Matrix_Algebra.o
	$(CC) $(CFLAGS) -o $@ $^

driver_mn: driver_mn.o Matrix_Algebra.o
	$(CC) $(CFLAGS) -o $@ $^

driver_33.o: driver_33.c Matrix_Algebra.o $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $<

driver_mn.o: driver_mn.c Matrix_Algebra.o $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $<

Matrix_Algebra.o: Matrix_Algebra.c $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $<

.PHONY: clean
clean:
	$(RM) $(TESTBEDS) *.o
