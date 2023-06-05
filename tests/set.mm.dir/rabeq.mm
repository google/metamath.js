include "nfcv.mm";
include "rabeqf.mm";

theorem rabeq(wph: wff ph, vx: setvar x, cA: class A, cB: class B) {

  disjoint A x;
  disjoint B x;



  do {
    wph;
    vx;
    cA;
    cB;
    vx;
    cA;
    nfcv;
    vx;
    cB;
    nfcv;
    rabeqf;
  };

  return |- "( A = B -> { x e. A | ph } = { x e. B | ph } )";
}
