include "tb.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "df-b.mm";
include "df-a.mm";
include "ax-r1.mm";
include "oran.mm";
include "con2.mm";
include "2or.mm";
include "ax-r2.mm";

theorem dfb(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    tb;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wo;
    wn;
    #;
    wva;
    wvb;
    wo;
    #;
    wn;
    #;
    wo;
    wva;
    wvb;
    wa;
    #;
    @0;
    @1;
    wa;
    #;
    wo;
    wva;
    wvb;
    df-b;
    @2;
    @5;
    @4;
    @6;
    @5;
    @2;
    wva;
    wvb;
    df-a;
    ax-r1;
    @3;
    @6;
    wva;
    wvb;
    oran;
    con2;
    2or;
    ax-r2;
  };

  return $|- ( a == b ) = ( ( a ^ b ) v ( a ' ^ b ' ) )$;
}
