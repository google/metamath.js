include "wo.mm";
include "wa.mm";
include "orcom.mm";
include "leor.mm";
include "ler.mm";
include "mli.mm";
include "tr.mm";
include "lan.mm";
include "cm.mm";

theorem testmod3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {





  do {
    wva;
    wvc;
    wva;
    wo;
    #;
    wvb;
    wvc;
    wo;
    wvd;
    wva;
    wo;
    wa;
    #;
    wo;
    #;
    wvb;
    wvd;
    wva;
    wvc;
    wo;
    wvb;
    wvd;
    wo;
    wa;
    wo;
    wa;
    #;
    wa;
    #;
    wo;
    #;
    @2;
    wva;
    @3;
    wo;
    #;
    wa;
    #;
    @5;
    @2;
    @3;
    wva;
    wo;
    #;
    wa;
    #;
    @7;
    @5;
    @4;
    wva;
    wo;
    @9;
    wva;
    @4;
    orcom;
    @2;
    @3;
    wva;
    wva;
    @0;
    @1;
    wva;
    wvc;
    leor;
    ler;
    mli;
    tr;
    @8;
    @6;
    @2;
    @3;
    wva;
    orcom;
    lan;
    tr;
    cm;
  };

  return $|-$ $( ( ( c v a ) v ( ( b v c ) ^ ( d v a ) ) ) ^ ( a v ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) ) ) = ( a v ( ( ( c v a ) v ( ( b v c ) ^ ( d v a ) ) ) ^ ( b ^ ( d v ( ( a v c ) ^ ( b v d ) ) ) ) ) )$;
}
