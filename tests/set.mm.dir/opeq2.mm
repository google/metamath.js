include "wceq.mm";
include "cvv.mm";
include "wcel.mm";
include "wa.mm";
include "csn.mm";
include "cpr.mm";
include "c0.mm";
include "cif.mm";
include "cop.mm";
include "eleq1.mm";
include "anbi2d.mm";
include "preq2.mm";
include "preq2d.mm";
include "ifbieq1d.mm";
include "dfopif.mm";
include "3eqtr4g.mm";

theorem opeq2(cA: class A, cB: class B, cC: class C) {





  do {
    cA;
    cB;
    wceq;
    #;
    cC;
    cvv;
    wcel;
    #;
    cA;
    cvv;
    wcel;
    #;
    wa;
    #;
    cC;
    csn;
    #;
    cC;
    cA;
    cpr;
    #;
    cpr;
    #;
    c0;
    cif;
    @1;
    cB;
    cvv;
    wcel;
    #;
    wa;
    #;
    @4;
    cC;
    cB;
    cpr;
    #;
    cpr;
    #;
    c0;
    cif;
    cC;
    cA;
    cop;
    cC;
    cB;
    cop;
    @0;
    @3;
    @8;
    @6;
    @10;
    c0;
    @0;
    @2;
    @7;
    @1;
    cA;
    cB;
    cvv;
    eleq1;
    anbi2d;
    @0;
    @5;
    @9;
    @4;
    cA;
    cB;
    cC;
    preq2;
    preq2d;
    ifbieq1d;
    cC;
    cA;
    dfopif;
    cC;
    cB;
    dfopif;
    3eqtr4g;
  };

  return |- "( A = B -> <. C , A >. = <. C , B >. )";
}
