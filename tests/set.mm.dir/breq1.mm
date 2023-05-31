include "wceq.mm";
include "cop.mm";
include "wcel.mm";
include "wbr.mm";
include "opeq1.mm";
include "eleq1d.mm";
include "df-br.mm";
include "3bitr4g.mm";

theorem breq1(cA: $class$ A, cB: $class$ B, cC: $class$ C, cR: $class$ R) {





  do {
    cA;
    cB;
    wceq;
    #;
    cA;
    cC;
    cop;
    #;
    cR;
    wcel;
    cB;
    cC;
    cop;
    #;
    cR;
    wcel;
    cA;
    cC;
    cR;
    wbr;
    cB;
    cC;
    cR;
    wbr;
    @0;
    @1;
    @2;
    cR;
    cA;
    cB;
    cC;
    opeq1;
    eleq1d;
    cA;
    cC;
    cR;
    df-br;
    cB;
    cC;
    cR;
    df-br;
    3bitr4g;
  };

  return $|-$ $( A = B -> ( A R C <-> B R C ) )$;
}
