include "wn.mm";
include "tb.mm";
include "wt.mm";
include "ax-a1.mm";
include "ax-r1.mm";
include "lbi.mm";
include "ax-r2.mm";
include "wcon1.mm";

theorem wcon3(wva: $term$ a, wvb: $term$ b) {
  assume wcon3.1: $|- ( a ' == b ) = 1$;





  do {
    wva;
    wvb;
    wn;
    #;
    wva;
    wn;
    #;
    @0;
    wn;
    #;
    tb;
    @1;
    wvb;
    tb;
    wt;
    @2;
    wvb;
    @1;
    wvb;
    @2;
    wvb;
    ax-a1;
    ax-r1;
    lbi;
    wcon3.1;
    ax-r2;
    wcon1;
  };

  return $|-$ $( a == b ' ) = 1$;
}
