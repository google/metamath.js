include "wceq.mm";
include "cun.mm";
include "uneq1.mm";
include "uncom.mm";
include "3eqtr4g.mm";

theorem uneq2(cA: 'class' A, cB: 'class' B, cC: 'class' C) {





  do {
    cA;
    cB;
    wceq;
    cA;
    cC;
    cun;
    cB;
    cC;
    cun;
    cC;
    cA;
    cun;
    cC;
    cB;
    cun;
    cA;
    cB;
    cC;
    uneq1;
    cC;
    cA;
    uncom;
    cC;
    cB;
    uncom;
    3eqtr4g;
  };

  return '|-' "( A = B -> ( C u. A ) = ( C u. B ) )";
}
