include "wa.mm";
include "tb.mm";
include "wn.mm";
include "wo.mm";
include "wt.mm";
include "df-a.mm";
include "2bi.mm";
include "wr4.mm";
include "wr5-2v.mm";
include "ax-r2.mm";

theorem wran(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wran.1: $|- ( a == b ) = 1$;





  do {
    wva;
    wvc;
    wa;
    #;
    wvb;
    wvc;
    wa;
    #;
    tb;
    wva;
    wn;
    #;
    wvc;
    wn;
    #;
    wo;
    #;
    wn;
    #;
    wvb;
    wn;
    #;
    @3;
    wo;
    #;
    wn;
    #;
    tb;
    wt;
    @0;
    @5;
    @1;
    @8;
    wva;
    wvc;
    df-a;
    wvb;
    wvc;
    df-a;
    2bi;
    @4;
    @7;
    @2;
    @6;
    @3;
    wva;
    wvb;
    wran.1;
    wr4;
    wr5-2v;
    wr4;
    ax-r2;
  };

  return $|-$ $( ( a ^ c ) == ( b ^ c ) ) = 1$;
}
