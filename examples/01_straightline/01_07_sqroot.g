@rnd = float< ieee_64, ne >;

# return (((1.0 + (0.5 * x)) - ((0.125 * x) * x)) + (((0.0625 * x) * x) * x)) - ((((0.0390625 * x) * x) * x) * x);

p0 = 0.5;
p1 rnd= (0.5 * x);
p2 rnd= (rnd(0.125 * x) * x);
p3 rnd= (rnd(rnd(0.0625 * x) * x) * x);
p4 rnd= (rnd(rnd(rnd(0.0390625 * x) * x) * x) * x);
e = p0 + p1 - p2 + p3 - p4;

{ x in [0.0,1.0]
  -> e in ? }
