include "wceq.mm";
include "cv.mm";
include "wcel.mm";
include "wb.mm";
include "dfcleq.mm";
include "mpgbir.mm";

theorem eqriv(vx: 'setvar' x, cA: 'class' A, cB: 'class' B) {
  assume eqriv.1: |- "( x e. A <-> x e. B )";

  disjoint A x;
  disjoint B x;



  do {
    cA;
    cB;
    wceq;
    vx;
    cv;
    #;
    cA;
    wcel;
    @0;
    cB;
    wcel;
    wb;
    vx;
    vx;
    cA;
    cB;
    dfcleq;
    eqriv.1;
    mpgbir;
  };

  return '|-' "A = B";
}
