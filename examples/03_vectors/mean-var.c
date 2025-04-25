/* Compute mean and variance, while always having variance on-hand
 * i.e. at each iteration of the loop, you have avg
 * Question: Is this always correct for all iterations of `n`?
 */
void mean_var()
{

   float a [4] = { 1.0, 2.0, 3.0, 4.0 };
 
   int n = sizeof (a) / sizeof (a [0]);
 
   float avg = a [0];
   float var = 0.0;
 
   for (int i = 1; i < n; ++i) {
      float b = a [i] - avg;
      float c = 1.0 / (float) (i + 1);
      float d = ((float) i) * c;
 
      var += d * b * b;
      avg += c * b;
   }
 
   if (n > 1) {
      var /= (n - 1);
   }
}

int main()
{
	mean_var();
}
