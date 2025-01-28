# Results

## sqroot

When run without `requires \is_finite(x)`:
```
frama-c -wp -wp-rte -wp-model +float -wp-prover alt-ergo,gappa,colibri2,z3   -wp-fct sqroot 01_07_sqroot.c
[kernel] Parsing 01_07_sqroot.c (with preprocessing)
[rte:annot] annotating function sqroot
[wp] 15 goals scheduled
[wp] [Timeout] typed_sqroot_ensures (Qed 2ms) (Alt-Ergo)
[wp] [Timeout] typed_sqroot_assert_rte_is_nan_or_infinite_9 (Qed 0.70ms) (Alt-Ergo)
[wp] [Timeout] typed_sqroot_assert_rte_is_nan_or_infinite_12 (Qed 1ms) (Alt-Ergo)
[wp] [Timeout] typed_sqroot_assert_rte_is_nan_or_infinite_13 (Qed 0.81ms) (Alt-Ergo)
[wp] [Timeout] typed_sqroot_assert_rte_is_nan_or_infinite_14 (Qed 0.87ms) (Alt-Ergo)
[wp] Proved goals:   12 / 17
  Terminating:       1
  Unreachable:       1
  Qed:               0 (0.69ms-0.74ms-2ms)
  Alt-Ergo 2.4.2:    7 (452ms-865ms-1.5s)
  Colibri2 0.4:      2 (451ms-1.4s)
  Gappa 1.4.1:       1 (16ms)
  Timeout:           5
```

When run with `requires \is_finite(x)`

```
frama-c -wp -wp-rte -wp-model +float -wp-prover alt-ergo,gappa,colibri2,z3   -wp-fct sqroot 01_07_sqroot.c
[kernel] Parsing 01_07_sqroot.c (with preprocessing)
[rte:annot] annotating function sqroot
[wp] 16 goals scheduled
[wp] [Timeout] typed_sqroot_ensures (Qed 2ms) (Alt-Ergo)
[wp] Proved goals:   17 / 18
  Terminating:     1
  Unreachable:     1
  Qed:             1 (0.65ms-0.71ms-2ms)
  Gappa 1.4.1:    14 (9ms-86ms-212ms)
  Timeout:         1
```

But if you make the bound useless: `ensures -1.0 <= \result <= 2.0;`
then it works :(
