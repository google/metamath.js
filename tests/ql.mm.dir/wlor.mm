include "wo.mm";
include "tb.mm";
include "wt.mm";
include "ax-a2.mm";
include "2bi.mm";
include "wr5-2v.mm";
include "ax-r2.mm";

theorem wlor(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wlor.1: $|- ( a == b ) = 1$;





  do {
    wvc;
    wva;
    wo;
    #;
    wvc;
    wvb;
    wo;
    #;
    tb;
    wva;
    wvc;
    wo;
    #;
    wvb;
    wvc;
    wo;
    #;
    tb;
    wt;
    @0;
    @2;
    @1;
    @3;
    wvc;
    wva;
    ax-a2;
    wvc;
    wvb;
    ax-a2;
    2bi;
    wva;
    wvb;
    wvc;
    wlor.1;
    wr5-2v;
    ax-r2;
  };

  return $|- ( ( c v a ) == ( c v b ) ) = 1$;
}
