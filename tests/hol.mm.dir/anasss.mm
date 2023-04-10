include "kct.mm";
include "ax-cb1.mm";
include "wctl.mm";
include "id.mm";
include "ancoms.mm";
include "sylan.mm";
include "an32s.mm";

theorem anasss(ta: $term$ A, tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume an32s.1: $|- ( ( R , S ) , T ) |= A$;





  do {
    ts;
    tt;
    kct;
    tr;
    ta;
    ta;
    ts;
    tr;
    tt;
    ta;
    ts;
    tr;
    kct;
    tr;
    ts;
    kct;
    #;
    tt;
    tr;
    ts;
    @0;
    @0;
    @0;
    tt;
    ta;
    @0;
    tt;
    kct;
    an32s.1;
    ax-cb1;
    wctl;
    id;
    ancoms;
    an32s.1;
    sylan;
    an32s;
    ancoms;
  };

  return $|-$ $( R , ( S , T ) ) |= A$;
}
