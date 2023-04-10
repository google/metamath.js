include "wo.mm";
include "wa.mm";
include "mldual.mm";
include "ancom.mm";
include "lor.mm";
include "lea.mm";
include "ml2i.mm";
include "ax-a2.mm";
include "lan.mm";
include "3tr.mm";

theorem dp41lemd(wvp: $term$ p, wva0: $term$ a0, wva1: $term$ a1, wva2: $term$ a2, wvb0: $term$ b0, wvb1: $term$ b1, wvb2: $term$ b2, wvc0: $term$ c0, wvc1: $term$ c1, wvc2: $term$ c2, wvp2: $term$ p2) {
  assume dp41lem.1: $|- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )$;
  assume dp41lem.2: $|- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )$;
  assume dp41lem.3: $|- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )$;
  assume dp41lem.4: $|- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )$;
  assume dp41lem.5: $|- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) )$;
  assume dp41lem.6: $|- p2 =< ( a2 v b2 )$;





  do {
    wvc2;
    wva0;
    wvb1;
    wo;
    #;
    wvc2;
    wvc0;
    wvc1;
    wo;
    #;
    wa;
    #;
    wo;
    wa;
    wvc2;
    @0;
    wa;
    #;
    @2;
    wo;
    @3;
    @1;
    wvc2;
    wa;
    #;
    wo;
    #;
    wvc2;
    @1;
    @3;
    wo;
    #;
    wa;
    #;
    wvc2;
    @0;
    @1;
    mldual;
    @2;
    @4;
    @3;
    wvc2;
    @1;
    ancom;
    lor;
    @5;
    @3;
    @1;
    wo;
    #;
    wvc2;
    wa;
    wvc2;
    @8;
    wa;
    @7;
    wvc2;
    @1;
    @3;
    wvc2;
    @0;
    lea;
    ml2i;
    @8;
    wvc2;
    ancom;
    @8;
    @6;
    wvc2;
    @3;
    @1;
    ax-a2;
    lan;
    3tr;
    3tr;
  };

  return $|- ( c2 ^ ( ( a0 v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) ) = ( c2 ^ ( ( c0 v c1 ) v ( c2 ^ ( a0 v b1 ) ) ) )$;
}
