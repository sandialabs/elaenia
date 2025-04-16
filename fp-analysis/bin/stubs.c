/*
 * import from hwround.hpp in kv library:
 *   http://verifiedby.me/kv/
 */

#include <stdio.h>
#include <math.h>
#ifdef _MSC_VER
  #include <float.h>
#else
  #include <fenv.h>
#endif
#include <assert.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>

enum round_mode {
  NearestTiesToEven,
  ToZero,
  Up,
  Down,
  /* NearestTiesToAway */
};

static void change_round_mode(int mode) {
#ifdef _MSC_VER
  static unsigned int cw = 0;
  switch (mode) {
    case NearestTiesToEven:
      _controlfp_s(&cw, _RC_NEAR, _MCW_RC);
      break;
    case ToZero:
      _controlfp_s(&cw, _RC_CHOP, _MCW_RC);
      break;
    case Up:
      _controlfp_s(&cw, _RC_UP, _MCW_RC);
      break;
    case Down:
      _controlfp_s(&cw, _RC_DOWN, _MCW_RC);
      break;
    default: assert(0); break;
	}
#else
  switch (mode) {
    case NearestTiesToEven:
      fesetround(FE_TONEAREST);
      break;
    case ToZero:
      fesetround(FE_TOWARDZERO);
      break;
    case Up:
      fesetround(FE_UPWARD);
      break;
    case Down:
      fesetround(FE_DOWNWARD);
      break;
    default: assert(0); break;
  }
#endif
}

CAMLprim value addc(value mode, value x, value y) {
    volatile double r, x1 = Double_val(x), y1 = Double_val(y);
    change_round_mode(Int_val(mode));
    r = x1 + y1;
    change_round_mode(NearestTiesToEven);
    return caml_copy_double(r);
}

CAMLprim value subc(value mode, value x, value y) {
    volatile double r, x1 = Double_val(x), y1 = Double_val(y);
    change_round_mode(Int_val(mode));
    r = x1 - y1;
    change_round_mode(NearestTiesToEven);
    return caml_copy_double(r);
}

CAMLprim value mulc(value mode, value x, value y) {
    volatile double r, x1 = Double_val(x), y1 = Double_val(y);
    change_round_mode(Int_val(mode));
    r = x1 * y1;
    change_round_mode(NearestTiesToEven);
    return caml_copy_double(r);
}

CAMLprim value divc(value mode, value x, value y) {
    volatile double r, x1 = Double_val(x), y1 = Double_val(y);
    change_round_mode(Int_val(mode));
    r = x1 / y1;
    change_round_mode(NearestTiesToEven);
    return caml_copy_double(r);
}

CAMLprim value sqrtc(value mode, value x) {
    volatile double r, x1 = Double_val(x);
    change_round_mode(Int_val(mode));
    r = sqrt(x1);
    change_round_mode(NearestTiesToEven);
    return caml_copy_double(r);
}