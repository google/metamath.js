include "wo.mm";
include "wa.mm";
include "ax-a2.mm";
include "ran.mm";
include "ancom.mm";
include "mldual2i.mm";
include "3tr.mm";
include "ror.mm";
include "orcom.mm";

theorem mlduali(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume mlduali.1: $|- a =< c$;





  do {
    wva;
    wvb;
    wo;
    #;
    wvc;
    wa;
    #;
    wvc;
    wvb;
    wa;
    #;
    wva;
    wo;
    #;
    wvb;
    wvc;
    wa;
    #;
    wva;
    wo;
    wva;
    @4;
    wo;
    @1;
    wvb;
    wva;
    wo;
    #;
    wvc;
    wa;
    wvc;
    @5;
    wa;
    @3;
    @0;
    @5;
    wvc;
    wva;
    wvb;
    ax-a2;
    ran;
    @5;
    wvc;
    ancom;
    wva;
    wvb;
    wvc;
    mlduali.1;
    mldual2i;
    3tr;
    @2;
    @4;
    wva;
    wvc;
    wvb;
    ancom;
    ror;
    @4;
    wva;
    orcom;
    3tr;
  };

  return $|-$ $( ( a v b ) ^ c ) = ( a v ( b ^ c ) )$;
}
