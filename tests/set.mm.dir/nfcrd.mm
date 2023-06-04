include "wnfc.mm";
include "cv.mm";
include "wcel.mm";
include "wnf.mm";
include "nfcr.mm";
include "syl.mm";

theorem nfcrd(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y, cA: 'class' A) {
  assume nfcrd.1: |- "( ph -> F/_ x A )";

  disjoint x y;
  disjoint A y;



  do {
    wph;
    vx;
    cA;
    wnfc;
    vy;
    cv;
    cA;
    wcel;
    vx;
    wnf;
    nfcrd.1;
    vx;
    vy;
    cA;
    nfcr;
    syl;
  };

  return '|-' "( ph -> F/ x y e. A )";
}
