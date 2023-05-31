include "wo.mm";
include "wle2.mm";
include "tb.mm";
include "wt.mm";
include "df-le.mm";
include "ax-a3.mm";
include "ax-r1.mm";
include "rbi.mm";
include "ax-r2.mm";
include "wr5-2v.mm";

theorem wler(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wle.1: $|- ( a =<2 b ) = 1$;





  do {
    wva;
    wvb;
    wvc;
    wo;
    #;
    wle2;
    wva;
    @0;
    wo;
    #;
    @0;
    tb;
    #;
    wt;
    wva;
    @0;
    df-le;
    @2;
    wva;
    wvb;
    wo;
    #;
    wvc;
    wo;
    #;
    @0;
    tb;
    wt;
    @1;
    @4;
    @0;
    @4;
    @1;
    wva;
    wvb;
    wvc;
    ax-a3;
    ax-r1;
    rbi;
    @3;
    wvb;
    wvc;
    @3;
    wvb;
    tb;
    #;
    wva;
    wvb;
    wle2;
    #;
    wt;
    @6;
    @5;
    wva;
    wvb;
    df-le;
    ax-r1;
    wle.1;
    ax-r2;
    wr5-2v;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( a =<2 ( b v c ) ) = 1$;
}
