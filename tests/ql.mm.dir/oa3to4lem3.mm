include "wa.mm";
include "wo.mm";
include "wi1.mm";
include "oa3to4lem1.mm";
include "oa3to4lem2.mm";
include "le2an.mm";
include "lelor.mm";
include "le2or.mm";
include "lelan.mm";

theorem oa3to4lem3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d, wvg: $term$ g) {
  assume oa3to4lem.1: $|- a ' =< b$;
  assume oa3to4lem.2: $|- c ' =< d$;
  assume oa3to4lem.3: $|- g = ( ( a ^ b ) v ( c ^ d ) )$;





  do {
    wvb;
    wvd;
    wva;
    wvc;
    wa;
    #;
    wvb;
    wvd;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    wo;
    wva;
    wvg;
    wi1;
    #;
    wvc;
    wvg;
    wi1;
    #;
    @0;
    @4;
    @5;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    wo;
    wva;
    wvb;
    @4;
    @3;
    @8;
    wva;
    wvb;
    wvc;
    wvd;
    wvg;
    oa3to4lem.1;
    oa3to4lem.2;
    oa3to4lem.3;
    oa3to4lem1;
    #;
    wvd;
    @5;
    @2;
    @7;
    wva;
    wvb;
    wvc;
    wvd;
    wvg;
    oa3to4lem.1;
    oa3to4lem.2;
    oa3to4lem.3;
    oa3to4lem2;
    #;
    @1;
    @6;
    @0;
    wvb;
    @4;
    wvd;
    @5;
    @9;
    @10;
    le2an;
    lelor;
    le2an;
    le2or;
    lelan;
  };

  return $|-$ $( a ^ ( b v ( d ^ ( ( a ^ c ) v ( b ^ d ) ) ) ) ) =< ( a ^ ( ( a ->1 g ) v ( ( c ->1 g ) ^ ( ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) ) ) )$;
}
