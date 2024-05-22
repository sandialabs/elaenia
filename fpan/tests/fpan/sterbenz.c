/*@ requires \is_finite(y) && \is_finite(x);
  @ requires y/2. <= x <= 2.*y;
  @ ensures  \result == x-y;
*/
float sterbenz(float x, float y) {
  return x-y;
}

