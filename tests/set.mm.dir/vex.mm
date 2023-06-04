include "cv.mm";
include "cvv.mm";
include "wcel.mm";
include "weq.mm";
include "equid.mm";
include "df-v.mm";
include "abeq2i.mm";
include "mpbir.mm";

theorem vex(vx: 'setvar' x) {





  do {
    vx;
    cv;
    cvv;
    wcel;
    vx;
    vx;
    weq;
    #;
    vx;
    equid;
    @0;
    vx;
    cvv;
    vx;
    df-v;
    abeq2i;
    mpbir;
  };

  return '|-' "x e. _V";
}
