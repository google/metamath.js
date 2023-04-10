include "wi2.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "lea.mm";
include "letr.mm";
include "df2le2.mm";
include "ax-r1.mm";
include "ancom.mm";
include "ax-r2.mm";
include "lor.mm";
include "lbtr.mm";
include "ledi.mm";
include "lebi.mm";

theorem oadistc(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oadistc.1: $|- d =< ( ( a ->2 b ) ^ ( a ->2 c ) )$;
  assume oadistc.2: $|- ( ( a ->2 b ) ^ ( ( b v c ) ' v d ) ) =< ( ( ( a ->2 b ) ^ ( b v c ) ' ) v d )$;





  do {
    wva;
    wvb;
    wi2;
    #;
    wvb;
    wvc;
    wo;
    wn;
    #;
    wvd;
    wo;
    wa;
    #;
    @0;
    @1;
    wa;
    #;
    @0;
    wvd;
    wa;
    #;
    wo;
    #;
    @2;
    @3;
    wvd;
    wo;
    @5;
    oadistc.2;
    wvd;
    @4;
    @3;
    wvd;
    wvd;
    @0;
    wa;
    #;
    @4;
    @6;
    wvd;
    wvd;
    @0;
    wvd;
    @0;
    wva;
    wvc;
    wi2;
    #;
    wa;
    @0;
    oadistc.1;
    @0;
    @7;
    lea;
    letr;
    df2le2;
    ax-r1;
    wvd;
    @0;
    ancom;
    ax-r2;
    lor;
    lbtr;
    @0;
    @1;
    wvd;
    ledi;
    lebi;
  };

  return $|-$ $( ( a ->2 b ) ^ ( ( b v c ) ' v d ) ) = ( ( ( a ->2 b ) ^ ( b v c ) ' ) v ( ( a ->2 b ) ^ d ) )$;
}
