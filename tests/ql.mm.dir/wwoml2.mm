include "wn.mm";
include "wa.mm";
include "wo.mm";
include "tb.mm";
include "wt.mm";
include "df-le2.mm";
include "ax-r1.mm";
include "lan.mm";
include "lor.mm";
include "rbi.mm";
include "lbi.mm";
include "woml.mm";
include "3tr2.mm";

theorem wwoml2(wva: $term$ a, wvb: $term$ b) {
  assume wwoml2.1: $|- a =< b$;





  do {
    wva;
    wva;
    wn;
    #;
    wvb;
    wa;
    #;
    wo;
    #;
    wva;
    wvb;
    wo;
    #;
    tb;
    wva;
    @0;
    @3;
    wa;
    #;
    wo;
    #;
    @3;
    tb;
    @2;
    wvb;
    tb;
    wt;
    @2;
    @5;
    @3;
    @1;
    @4;
    wva;
    wvb;
    @3;
    @0;
    @3;
    wvb;
    wva;
    wvb;
    wwoml2.1;
    df-le2;
    #;
    ax-r1;
    lan;
    lor;
    rbi;
    @3;
    wvb;
    @2;
    @6;
    lbi;
    wva;
    wvb;
    woml;
    3tr2;
  };

  return $|- ( ( a v ( a ' ^ b ) ) == b ) = 1$;
}
