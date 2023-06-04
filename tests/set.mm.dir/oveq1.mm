include "wceq.mm";
include "cop.mm";
include "cfv.mm";
include "co.mm";
include "opeq1.mm";
include "fveq2d.mm";
include "df-ov.mm";
include "3eqtr4g.mm";

theorem oveq1(cA: 'class' A, cB: 'class' B, cC: 'class' C, cF: 'class' F) {





  do {
    cA;
    cB;
    wceq;
    #;
    cA;
    cC;
    cop;
    #;
    cF;
    cfv;
    cB;
    cC;
    cop;
    #;
    cF;
    cfv;
    cA;
    cC;
    cF;
    co;
    cB;
    cC;
    cF;
    co;
    @0;
    @1;
    @2;
    cF;
    cA;
    cB;
    cC;
    opeq1;
    fveq2d;
    cA;
    cC;
    cF;
    df-ov;
    cB;
    cC;
    cF;
    df-ov;
    3eqtr4g;
  };

  return '|-' "( A = B -> ( A F C ) = ( B F C ) )";
}
