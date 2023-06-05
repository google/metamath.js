include "wceq.mm";
include "cun.mm";
include "cv.mm";
include "wcel.mm";
include "wo.mm";
include "eleq2.mm";
include "orbi1d.mm";
include "elun.mm";
include "3bitr4g.mm";
include "eqrdv.mm";

theorem uneq1(cA: class A, cB: class B, cC: class C) {



  let vx: setvar x;

  do {
    cA;
    cB;
    wceq;
    #;
    vx;
    cA;
    cC;
    cun;
    #;
    cB;
    cC;
    cun;
    #;
    @0;
    vx;
    cv;
    #;
    cA;
    wcel;
    #;
    @3;
    cC;
    wcel;
    #;
    wo;
    @3;
    cB;
    wcel;
    #;
    @5;
    wo;
    @3;
    @1;
    wcel;
    @3;
    @2;
    wcel;
    @0;
    @4;
    @6;
    @5;
    cA;
    cB;
    @3;
    eleq2;
    orbi1d;
    @3;
    cA;
    cC;
    elun;
    @3;
    cB;
    cC;
    elun;
    3bitr4g;
    eqrdv;
  };

  return |- "( A = B -> ( A u. C ) = ( B u. C ) )";
}
