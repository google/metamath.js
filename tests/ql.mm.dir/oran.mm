include "wn.mm";
include "wo.mm";
include "wa.mm";
include "ax-a1.mm";
include "2or.mm";
include "df-a.mm";
include "ax-r4.mm";
include "3tr1.mm";

theorem oran(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wn;
    #;
    wvb;
    wn;
    #;
    wn;
    #;
    wo;
    #;
    @4;
    wn;
    #;
    wn;
    wva;
    wvb;
    wo;
    @0;
    @2;
    wa;
    #;
    wn;
    @4;
    ax-a1;
    wva;
    @1;
    wvb;
    @3;
    wva;
    ax-a1;
    wvb;
    ax-a1;
    2or;
    @6;
    @5;
    @0;
    @2;
    df-a;
    ax-r4;
    3tr1;
  };

  return $|-$ $( a v b ) = ( a ' ^ b ' ) '$;
}
