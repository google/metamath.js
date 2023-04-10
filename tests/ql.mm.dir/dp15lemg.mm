include "wo.mm";
include "wa.mm";
include "ror.mm";
include "2or.mm";
include "cm.mm";
include "orass.mm";
include "tr.mm";

theorem dp15lemg(wvd: $term$ d, wve: $term$ e, wva0: $term$ a0, wva1: $term$ a1, wva2: $term$ a2, wvb0: $term$ b0, wvb1: $term$ b1, wvb2: $term$ b2, wvc0: $term$ c0, wvc1: $term$ c1, wvp0: $term$ p0) {
  assume dp15lema.1: $|- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) )$;
  assume dp15lema.2: $|- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )$;
  assume dp15lema.3: $|- e = ( b0 ^ ( a0 v p0 ) )$;
  assume dp15lemg.4: $|- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )$;
  assume dp15lemg.5: $|- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )$;





  do {
    wva1;
    wva2;
    wo;
    wvb1;
    wvb2;
    wo;
    wa;
    #;
    wva0;
    wva2;
    wo;
    wvb0;
    wvb2;
    wo;
    wa;
    #;
    wvb1;
    wva0;
    wva1;
    wo;
    wa;
    #;
    wo;
    #;
    wo;
    #;
    wvc0;
    wvc1;
    @2;
    wo;
    #;
    wo;
    #;
    wvc0;
    wvc1;
    wo;
    @2;
    wo;
    #;
    @6;
    @4;
    wvc0;
    @0;
    @5;
    @3;
    dp15lemg.4;
    wvc1;
    @1;
    @2;
    dp15lemg.5;
    ror;
    2or;
    cm;
    @7;
    @6;
    wvc0;
    wvc1;
    @2;
    orass;
    cm;
    tr;
  };

  return $|- ( ( ( a1 v a2 ) ^ ( b1 v b2 ) ) v ( ( ( a0 v a2 ) ^ ( b0 v b2 ) ) v ( b1 ^ ( a0 v a1 ) ) ) ) = ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) )$;
}
