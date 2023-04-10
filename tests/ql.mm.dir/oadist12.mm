include "wo.mm";
include "wi2.mm";
include "wa.mm";
include "wi1.mm";
include "u12lem.mm";
include "oadist2.mm";

theorem oadist12(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
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
    wi1;
    @0;
    @1;
    u12lem;
    oadist2;
  };

  return $|- ( ( a ->2 b ) ^ ( ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) v ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) = ( ( ( a ->2 b ) ^ ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) v ( ( a ->2 b ) ^ ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) )$;
}
