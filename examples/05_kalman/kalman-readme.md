# Kalman Filter Verification

NOTA BENE: This is based off work by Ariel Kellison, her repository of
the initial results can be found [here](https://github.com/ak-2485/Kalman_Filter)
and her other floating-point verification work (along with Andrew
Appel), VCFloat, can be found [here](https://github.com/VeriNum/vcfloat)

The examples, in increasing order of complexity, are:

1. gold - the simplest Kalman filter example (alpha-beta filter) which
   models weighing a gold bar on a noisy scale; the mass does not
   change.
2. flow - measuring the mass of a tank of water with constant, but
   unknown, flow.
3. kettle - measuring the temperature of water being heated by a kettle.
4. kettle_union - Same as kettle, but using a union type.
5. gps - tracking the position of an object in one dimension by tracking
   position, velocity, and acceleration.
6. kettle_adaptive. Similar to kettle, but adaptive in detecting a
   change in phenomena (meaning: the heating element switches on).


## Further Reading
- https://www.prismmodelchecker.org/papers/faoc-kf.pdf
- https://www.cs.princeton.edu/~appel/papers/ecosystem.pdf
