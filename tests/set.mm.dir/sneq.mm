include "wceq.mm";
include "cv.mm";
include "cab.mm";
include "csn.mm";
include "eqeq2.mm";
include "abbidv.mm";
include "df-sn.mm";
include "3eqtr4g.mm";

theorem sneq(cA: class A, cB: class B) {



  let vx: setvar x;

  do {
    cA;
    cB;
    wceq;
    #;
    vx;
    cv;
    #;
    cA;
    wceq;
    #;
    vx;
    cab;
    @1;
    cB;
    wceq;
    #;
    vx;
    cab;
    cA;
    csn;
    cB;
    csn;
    @0;
    @2;
    @3;
    vx;
    cA;
    cB;
    @1;
    eqeq2;
    abbidv;
    vx;
    cA;
    df-sn;
    vx;
    cB;
    df-sn;
    3eqtr4g;
  };

  return |- "( A = B -> { A } = { B } )";
}
