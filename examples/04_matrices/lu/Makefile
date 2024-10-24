CC = clang
CFLAGS = -g -Wall

HEADERS = Matrix_Algebra.h

TESTBEDS = driver

all: $(TESTBEDS)

driver: driver.o Matrix_Algebra.o
	$(CC) $(CFLAGS) -o $@ $^

driver.o: driver.c Matrix_Algebra.o $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $<

Matrix_Algebra.o: Matrix_Algebra.c $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $<

.PHONY: clean
clean:
	$(RM) $(TESTBEDS) *.o *.vos *.vok *.vo
