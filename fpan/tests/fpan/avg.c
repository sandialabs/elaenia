/*@ ensures \result == \abs(x); */
double abs(double x){
  if (x >= 0) return x;
  else return (-x);
}

/*@ axiomatic Floor {
  @  logic integer floor (real x);
  @  axiom floor_prop: \forall real x; floor(x) <= x < floor(x)+1;
  @ } */

/*@ logic real ulp_d (real x) =
  @ \let e = 1+ floor (\log(\abs(x)) / \log(2)); 
  @    \pow(2,\max(e-53,-1074)); */

/*@ logic real l_average (real x, real y) = 
  @   \let same_sign =
  @     (x >= 0) ? ((y >=0) ? \true : \false) : ((y >=0) ? \false : \true);
  @   (same_sign) ? ((\abs(x) <= \abs(y)) ?
  @     \round_double(\NearestEven, x+\round_double(\NearestEven, 
  @           \round_double(\NearestEven, y-x)/2))  :                   
  @        \round_double(\NearestEven, y+\round_double(\NearestEven, 
  @           \round_double(\NearestEven, x-y)/2))) :
  @     \round_double(\NearestEven,\round_double(\NearestEven, x+y)/2);
  @ */

/*@  lemma average_sym: \forall double x; \forall double y; 
  @        l_average(x,y) == l_average (y,x);
  @  lemma average_sym_opp: \forall double x; \forall double y; 
  @         l_average(-x,-y) == - l_average (x,y);
  @
  @ lemma average_props: \forall double x; \forall double y;
  @        \abs(l_average(x,y) - (x+y)/2) <= 3./2*ulp_d((x+y)/2)
  @   &&  (\min(x,y) <= l_average(x,y) <= \max(x,y))
  @   && (0 <= (x+y)/2 ==> 0 <= l_average(x,y))     
  @   && ((x+y)/2 <= 0 ==> l_average(x,y) <= 0)
  @   && ((x+y)/2==0 ==> l_average(x,y)==0)
  @   && (0x1p-1074 <= \abs((x+y)/2) ==> l_average(x,y) != 0);
  @ */


/*@   ensures \result == l_average(x,y);
  @   ensures \abs((\result - (x+y)/2)) <= 3./2*ulp_d((x+y)/2);
  @   ensures \min(x,y) <= \result <= \max(x,y);
  @   ensures 0 <= (x+y)/2 ==> 0 <= \result;     
  @   ensures (x+y)/2 <= 0 ==> \result <= 0;
  @   ensures (x+y)/2 == 0 ==> \result == 0;
  @   ensures 0x1p-1074 <= \abs((x+y)/2) ==> \result != 0;
  @ */
double average(double x, double y) {
  int same_sign;
  double r;
  if (x >= 0) {
    if (y >=0) same_sign=1;
    else same_sign=0; }
  else {
    if (y >=0) same_sign=0;
    else same_sign=1; }
  if (same_sign ==1) {
    if (abs(x) <= abs(y)) r=x+(y-x)/2;
    else r=y+(x-y)/2; }
  else r=(x+y)/2;
  //@ assert r==l_average(x,y);
  return r;
}
