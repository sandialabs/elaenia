/*
 * Analyze with "make frama-c"
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef __FRAMAC__
#include "__fc_builtin.h"
#endif

/* Eva can check a limited number of ACSL specs. In this case,
 * it can verify that "\assigns nothing" holds. */
/*@ requires \valid_read(name);
    requires \is_finite(value);
    assigns \nothing;
 */
void checkOverflow(const double value, const char* name)
{
  /* HUGE_VALF/HUGE_VALL are only available with certain features. If they're
   * not, then HUGE_VAL should be available */
#ifdef HUGE_VALF
  if(value == HUGE_VALF || value == HUGE_VALL) { // || value == -HUGE_VALF || value == -HUGE_VALL
    printf("Error: Overflow detected in %s\n", name);
    exit(EXIT_FAILURE);
  }
#else
  if(value == HUGE_VAL) { // || value == -HUGE_VAL
    printf("Error: Overflow detected in %s\n", name);
    exit(EXIT_FAILURE);
  }
#endif // HUGE_VALF
// Note: We recommend this be included as well as just +/- infinity
/*
  if (isnan(value)){
    printf("Error: Overflow detected in %s\n", name);
    exit(EXIT_FAILURE);
  }
*/
}

#ifdef __FRAMAC__
int fc_main(int argc, char *argv[])
{
  double x = Frama_C_double_interval(-DBL_MAX,DBL_MAX);
  checkOverflow(x, "fc_main");
  x = strtod("1", NULL);
  checkOverflow(x, "Eva cannot prove the string '1' is finite");
  checkOverflow(NAN, "Checking for NaN");
  checkOverflow(-INFINITY, "Checking for -Infinity");
  return 0;
}
#endif

int main(int argc, char *argv[])
{
  srand(42);
  int i;
  double x;
  // An incomplete way to randomly generate FP numbers from [0, 1 000 000]
  for (i = 0; i < 1000; i++) {
    double x = (double)rand()/(double)(RAND_MAX/1000000.0);
    checkOverflow(x, "main");
  }
  x = strtod("nan", NULL);
  checkOverflow(x, "Checking for NaN");
  x = strtod("-Inf", NULL);
  checkOverflow(x, "Checking for -Infinity");
  printf("All x are valid\n");
  return 0;
}
