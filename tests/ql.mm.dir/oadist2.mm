include "wo.mm";
include "wi2.mm";
include "wa.mm";
include "wi0.mm";
include "bile.mm";
include "oadist2a.mm";

theorem oadist2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oadist2.1: $|- ( d v ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) = ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) )$;





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
    wo;
    @0;
    @1;
    wi0;
    oadist2.1;
    bile;
    oadist2a;
  };

  return $|- ( ( a ->2 b ) ^ ( d v ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) = ( ( ( a ->2 b ) ^ d ) v ( ( a ->2 b ) ^ ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) )$;
}
