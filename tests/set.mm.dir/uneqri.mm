include "cun.mm";
include "cv.mm";
include "wcel.mm";
include "wo.mm";
include "elun.mm";
include "bitri.mm";
include "eqriv.mm";

theorem uneqri(vx: setvar x, cA: class A, cB: class B, cC: class C) {
  assume uneqri.1: |- "( ( x e. A \\/ x e. B ) <-> x e. C )";

  disjoint A x;
  disjoint B x;
  disjoint C x;



  do {
    vx;
    cA;
    cB;
    cun;
    #;
    cC;
    vx;
    cv;
    #;
    @0;
    wcel;
    @1;
    cA;
    wcel;
    @1;
    cB;
    wcel;
    wo;
    @1;
    cC;
    wcel;
    @1;
    cA;
    cB;
    elun;
    uneqri.1;
    bitri;
    eqriv;
  };

  return |- "( A u. B ) = C";
}
