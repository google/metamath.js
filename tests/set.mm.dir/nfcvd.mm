include "wnfc.mm";
include "nfcv.mm";
include "a1i.mm";

theorem nfcvd(wph: wff ph, vx: setvar x, cA: class A) {

  disjoint A x;
  disjoint x y;
  disjoint A y;

  let vy: setvar y;

  do {
    vx;
    cA;
    wnfc;
    wph;
    vx;
    cA;
    nfcv;
    a1i;
  };

  return |- "( ph -> F/_ x A )";
}
