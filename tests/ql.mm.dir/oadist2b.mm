include "wo.mm";
include "wi2.mm";
include "wa.mm";
include "wi1.mm";
include "wi0.mm";
include "u12lem.mm";
include "ax-r1.mm";
include "lbtr.mm";
include "leor.mm";
include "lel2or.mm";
include "oadist2a.mm";

theorem oadist2b(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oadist2b.1: $|- d =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) )$;





  do {
    wva;
    wvb;
    wvc;
    wvd;
    wvd;
    wvb;
    wvc;
    wo;
    #;
    wva;
    wvb;
    wi2;
    wva;
    wvc;
    wi2;
    wa;
    #;
    wi2;
    #;
    wo;
    @0;
    @1;
    wi1;
    #;
    @2;
    wo;
    #;
    @0;
    @1;
    wi0;
    #;
    wvd;
    @4;
    @2;
    wvd;
    @5;
    @4;
    oadist2b.1;
    @4;
    @5;
    @0;
    @1;
    u12lem;
    #;
    ax-r1;
    lbtr;
    @2;
    @3;
    leor;
    lel2or;
    @6;
    lbtr;
    oadist2a;
  };

  return $|-$ $( ( a ->2 b ) ^ ( d v ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) = ( ( ( a ->2 b ) ^ d ) v ( ( a ->2 b ) ^ ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) )$;
}
