include "wceq.mm";
include "cpr.mm";
include "preq1.mm";
include "prcom.mm";
include "3eqtr4g.mm";

theorem preq2(cA: class A, cB: class B, cC: class C) {





  do {
    cA;
    cB;
    wceq;
    cA;
    cC;
    cpr;
    cB;
    cC;
    cpr;
    cC;
    cA;
    cpr;
    cC;
    cB;
    cpr;
    cA;
    cB;
    cC;
    preq1;
    cC;
    cA;
    prcom;
    cC;
    cB;
    prcom;
    3eqtr4g;
  };

  return |- "( A = B -> { C , A } = { C , B } )";
}
