include "wi2.mm";
include "bile.mm";

theorem distoah1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d, wve: $term$ e, wvf: $term$ f) {
  assume distoa.1: $|- d = ( a ->2 b )$;
  assume distoa.2: $|- e = ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) )$;
  assume distoa.3: $|- f = ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) )$;





  do {
    wvd;
    wva;
    wvb;
    wi2;
    distoa.1;
    bile;
  };

  return $|- d =< ( a ->2 b )$;
}
