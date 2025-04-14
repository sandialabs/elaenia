#include "daed_builtins.h"

int main() {
	double x, tmp;

    x = DBETWEEN(0,10);

	if (((x * x) - x) >= 0.0) {
		tmp = x / 10.0;
	} else {
		tmp = (x * x) + 2.0;
	}
	return tmp;
}
