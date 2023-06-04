include "wceq.mm";
include "cop.mm";
include "cfv.mm";
include "co.mm";
include "opeq2.mm";
include "fveq2d.mm";
include "df-ov.mm";
include "3eqtr4g.mm";

theorem oveq2(cA: 'class' A, cB: 'class' B, cC: 'class' C, cF: 'class' F) {





  do {
    cA;
    cB;
    wceq;
    #;
    cC;
    cA;
    cop;
    #;
    cF;
    cfv;
    cC;
    cB;
    cop;
    #;
    cF;
    cfv;
    cC;
    cA;
    cF;
    co;
    cC;
    cB;
    cF;
    co;
    @0;
    @1;
    @2;
    cF;
    cA;
    cB;
    cC;
    opeq2;
    fveq2d;
    cC;
    cA;
    cF;
    df-ov;
    cC;
    cB;
    cF;
    df-ov;
    3eqtr4g;
  };

  return '|-' "( A = B -> ( C F A ) = ( C F B ) )";
}
