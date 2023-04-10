include "wi2.mm";
include "wa.mm";
include "wo.mm";
include "oagen1.mm";
include "bile.mm";
include "anidm.mm";
include "ax-r1.mm";
include "ran.mm";
include "anass.mm";
include "ax-r2.mm";
include "leor.mm";
include "bltr.mm";
include "letr.mm";
include "ledi.mm";
include "lebi.mm";

theorem oadist(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oadist.1: $|- d =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) )$;





  do {
    wva;
    wvb;
    wi2;
    #;
    wvd;
    @0;
    wva;
    wvc;
    wi2;
    #;
    wa;
    #;
    wo;
    wa;
    #;
    @0;
    wvd;
    wa;
    #;
    @0;
    @2;
    wa;
    #;
    wo;
    #;
    @3;
    @2;
    @6;
    @3;
    @2;
    wva;
    wvb;
    wvc;
    wvd;
    oadist.1;
    oagen1;
    bile;
    @2;
    @5;
    @6;
    @2;
    @0;
    @0;
    wa;
    #;
    @1;
    wa;
    @5;
    @0;
    @7;
    @1;
    @7;
    @0;
    @0;
    anidm;
    ax-r1;
    ran;
    @0;
    @0;
    @1;
    anass;
    ax-r2;
    @5;
    @4;
    leor;
    bltr;
    letr;
    @0;
    wvd;
    @2;
    ledi;
    lebi;
  };

  return $|- ( ( a ->2 b ) ^ ( d v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) = ( ( ( a ->2 b ) ^ d ) v ( ( a ->2 b ) ^ ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )$;
}
