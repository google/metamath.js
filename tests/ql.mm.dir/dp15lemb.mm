include "dp15lema.mm";
include "ax-arg.mm";

theorem dp15lemb(wvd: $term$ d, wve: $term$ e, wva0: $term$ a0, wva1: $term$ a1, wva2: $term$ a2, wvb0: $term$ b0, wvb1: $term$ b1, wvb2: $term$ b2, wvp0: $term$ p0) {
  assume dp15lema.1: $|- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) )$;
  assume dp15lema.2: $|- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )$;
  assume dp15lema.3: $|- e = ( b0 ^ ( a0 v p0 ) )$;





  do {
    wva0;
    wva1;
    wvd;
    wve;
    wvb1;
    wvb2;
    wvd;
    wve;
    wva0;
    wva1;
    wva2;
    wvb0;
    wvb1;
    wvb2;
    wvp0;
    dp15lema.1;
    dp15lema.2;
    dp15lema.3;
    dp15lema;
    ax-arg;
  };

  return $|-$ $( ( a0 v a1 ) ^ ( e v b1 ) ) =< ( ( ( a0 v d ) ^ ( e v b2 ) ) v ( ( a1 v d ) ^ ( b1 v b2 ) ) )$;
}
