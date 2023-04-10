include "wo.mm";
include "wa.mm";
include "id.mm";
include "dp41lemm.mm";

theorem dp41(wva0: $term$ a0, wva1: $term$ a1, wva2: $term$ a2, wvb0: $term$ b0, wvb1: $term$ b1, wvb2: $term$ b2, wvc0: $term$ c0, wvc1: $term$ c1, wvc2: $term$ c2, wvp2: $term$ p2) {
  assume dp41.1: $|- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )$;
  assume dp41.2: $|- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )$;
  assume dp41.3: $|- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )$;
  assume dp41.4: $|- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) )$;
  assume dp41.5: $|- p2 =< ( a2 v b2 )$;





  do {
    wva0;
    wvb0;
    wo;
    wva1;
    wvb1;
    wo;
    wa;
    wva2;
    wvb2;
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
    wvc2;
    wvp2;
    dp41.1;
    dp41.2;
    dp41.3;
    @0;
    id;
    dp41.4;
    dp41.5;
    dp41lemm;
  };

  return $|- c2 =< ( c0 v c1 )$;
}
