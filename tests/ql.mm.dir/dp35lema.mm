include "wo.mm";
include "wa.mm";
include "leo.mm";
include "dp35lembb.mm";
include "lear.mm";
include "letr.mm";
include "lel2or.mm";

theorem dp35lema(wvp: $term$ p, wva0: $term$ a0, wva1: $term$ a1, wva2: $term$ a2, wvb0: $term$ b0, wvb1: $term$ b1, wvb2: $term$ b2, wvc0: $term$ c0, wvc1: $term$ c1, wvc2: $term$ c2, wvp0: $term$ p0) {
  assume dp35lem.1: $|- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )$;
  assume dp35lem.2: $|- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )$;
  assume dp35lem.3: $|- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )$;
  assume dp35lem.4: $|- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )$;
  assume dp35lem.5: $|- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )$;





  do {
    wvb1;
    wvb1;
    wva0;
    wva1;
    wo;
    wvc0;
    wvc1;
    wo;
    wa;
    #;
    wo;
    #;
    wvb0;
    wva0;
    wvp0;
    wo;
    wa;
    #;
    wvb1;
    @0;
    leo;
    @2;
    wvb0;
    @1;
    wa;
    @1;
    wvp;
    wva0;
    wva1;
    wva2;
    wvb0;
    wvb1;
    wvb2;
    wvc0;
    wvc1;
    wvc2;
    wvp0;
    dp35lem.1;
    dp35lem.2;
    dp35lem.3;
    dp35lem.4;
    dp35lem.5;
    dp35lembb;
    wvb0;
    @1;
    lear;
    letr;
    lel2or;
  };

  return $|- ( b1 v ( b0 ^ ( a0 v p0 ) ) ) =< ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) )$;
}
