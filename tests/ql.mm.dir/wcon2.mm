include "wn.mm";
include "tb.mm";
include "wt.mm";
include "conb.mm";
include "ax-a1.mm";
include "rbi.mm";
include "ax-r1.mm";
include "ax-r2.mm";

theorem wcon2(wva: $term$ a, wvb: $term$ b) {
  assume wcon2.1: $|- ( a == b ' ) = 1$;





  do {
    wva;
    wn;
    #;
    wvb;
    tb;
    #;
    wva;
    wvb;
    wn;
    #;
    tb;
    #;
    wt;
    @1;
    @0;
    wn;
    #;
    @2;
    tb;
    #;
    @3;
    @0;
    wvb;
    conb;
    @3;
    @5;
    wva;
    @4;
    @2;
    wva;
    ax-a1;
    rbi;
    ax-r1;
    ax-r2;
    wcon2.1;
    ax-r2;
  };

  return $|-$ $( a ' == b ) = 1$;
}
