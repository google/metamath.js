include "wceq.mm";
include "cpr.mm";
include "preq1.mm";
include "preq2.mm";
include "sylan9eq.mm";

theorem preq12(cA: 'class' A, cB: 'class' B, cC: 'class' C, cD: 'class' D) {





  do {
    cA;
    cC;
    wceq;
    cB;
    cD;
    wceq;
    cA;
    cB;
    cpr;
    cC;
    cB;
    cpr;
    cC;
    cD;
    cpr;
    cA;
    cC;
    cB;
    preq1;
    cB;
    cD;
    cC;
    preq2;
    sylan9eq;
  };

  return '|-' "( ( A = C /\\ B = D ) -> { A , B } = { C , D } )";
}
