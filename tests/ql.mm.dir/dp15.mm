include "wo.mm";
include "wa.mm";
include "id.mm";
include "dp15lemh.mm";

theorem dp15(wva0: $term$ a0, wva1: $term$ a1, wva2: $term$ a2, wvb0: $term$ b0, wvb1: $term$ b1, wvb2: $term$ b2, wvc0: $term$ c0, wvc1: $term$ c1, wvp0: $term$ p0) {
  assume dp15.1: $|- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )$;
  assume dp15.2: $|- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )$;
  assume dp15.3: $|- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )$;





  do {
    wva2;
    wva0;
    wva1;
    wvb1;
    wo;
    wa;
    wo;
    #;
    wvb0;
    wva0;
    wvp0;
    wo;
    wa;
    #;
    wva0;
    wva1;
    wva2;
    wvb0;
    wvb1;
    wvb2;
    wvc0;
    wvc1;
    wvp0;
    @0;
    id;
    dp15.3;
    @1;
    id;
    dp15.1;
    dp15.2;
    dp15lemh;
  };

  return $|- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) ) =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) )$;
}
