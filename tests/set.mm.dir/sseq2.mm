include "wss.mm";
include "wa.mm";
include "wi.mm";
include "wceq.mm";
include "wb.mm";
include "sstr2.mm";
include "com12.mm";
include "anim12i.mm";
include "eqss.mm";
include "dfbi2.mm";
include "3imtr4i.mm";

theorem sseq2(cA: $class$ A, cB: $class$ B, cC: $class$ C) {





  do {
    cA;
    cB;
    wss;
    #;
    cB;
    cA;
    wss;
    #;
    wa;
    cC;
    cA;
    wss;
    #;
    cC;
    cB;
    wss;
    #;
    wi;
    #;
    @3;
    @2;
    wi;
    #;
    wa;
    cA;
    cB;
    wceq;
    @2;
    @3;
    wb;
    @0;
    @4;
    @1;
    @5;
    @2;
    @0;
    @3;
    cC;
    cA;
    cB;
    sstr2;
    com12;
    @3;
    @1;
    @2;
    cC;
    cB;
    cA;
    sstr2;
    com12;
    anim12i;
    cA;
    cB;
    eqss;
    @2;
    @3;
    dfbi2;
    3imtr4i;
  };

  return $|-$ $( A = B -> ( C C_ A <-> C C_ B ) )$;
}
