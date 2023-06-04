include "nfcv.mm";
include "nfel.mm";

theorem nfel2(vx: 'setvar' x, cA: 'class' A, cB: 'class' B) {
  assume nfeq2.1: |- "F/_ x B";

  disjoint A x;



  do {
    vx;
    cA;
    cB;
    vx;
    cA;
    nfcv;
    nfeq2.1;
    nfel;
  };

  return '|-' "F/ x A e. B";
}
