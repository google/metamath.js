include "wi1.mm";
include "wa.mm";
include "wo.mm";
include "wt.mm";
include "r3a.mm";
include "ud1lem0b.mm";
include "lan.mm";
include "2or.mm";
include "anidm.mm";
include "u1lemoa.mm";
include "3tr.mm";

theorem oi3oa3lem1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume oi3oa3lem1.1: $|- 1 = ( b == a )$;





  do {
    wva;
    wvc;
    wi1;
    #;
    wvb;
    wvc;
    wi1;
    #;
    wa;
    #;
    wva;
    wvb;
    wa;
    #;
    wo;
    @0;
    @0;
    wa;
    #;
    wva;
    wva;
    wa;
    #;
    wo;
    @0;
    wva;
    wo;
    wt;
    @2;
    @4;
    @3;
    @5;
    @1;
    @0;
    @0;
    wvb;
    wva;
    wvc;
    wvb;
    wva;
    oi3oa3lem1.1;
    r3a;
    #;
    ud1lem0b;
    lan;
    wvb;
    wva;
    wva;
    @6;
    lan;
    2or;
    @4;
    @0;
    @5;
    wva;
    @0;
    anidm;
    wva;
    anidm;
    2or;
    wva;
    wvc;
    u1lemoa;
    3tr;
  };

  return $|-$ $( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( a ^ b ) ) = 1$;
}
