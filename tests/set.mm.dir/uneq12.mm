include "wceq.mm";
include "cun.mm";
include "uneq1.mm";
include "uneq2.mm";
include "sylan9eq.mm";

theorem uneq12(cA: 'class' A, cB: 'class' B, cC: 'class' C, cD: 'class' D) {





  do {
    cA;
    cB;
    wceq;
    cC;
    cD;
    wceq;
    cA;
    cC;
    cun;
    cB;
    cC;
    cun;
    cB;
    cD;
    cun;
    cA;
    cB;
    cC;
    uneq1;
    cC;
    cD;
    cB;
    uneq2;
    sylan9eq;
  };

  return '|-' "( ( A = B /\\ C = D ) -> ( A u. C ) = ( B u. D ) )";
}
