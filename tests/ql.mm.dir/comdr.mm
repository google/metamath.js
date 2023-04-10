include "wn.mm";
include "wa.mm";
include "wo.mm";
include "df-a.mm";
include "oran.mm";
include "con2.mm";
include "2or.mm";
include "ax-r4.mm";
include "ax-r2.mm";
include "df-c1.mm";
include "comcom5.mm";

theorem comdr(wva: $term$ a, wvb: $term$ b) {
  assume comdr.1: $|- a = ( ( a v b ) ^ ( a v b ' ) )$;





  do {
    wva;
    wvb;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wva;
    @0;
    @1;
    wa;
    #;
    @0;
    @1;
    wn;
    wa;
    #;
    wo;
    #;
    wva;
    wva;
    wvb;
    wo;
    #;
    wva;
    @1;
    wo;
    #;
    wa;
    #;
    @4;
    wn;
    #;
    comdr.1;
    @7;
    @5;
    wn;
    #;
    @6;
    wn;
    #;
    wo;
    #;
    wn;
    @8;
    @5;
    @6;
    df-a;
    @11;
    @4;
    @9;
    @2;
    @10;
    @3;
    @5;
    @2;
    wva;
    wvb;
    oran;
    con2;
    @6;
    @3;
    wva;
    @1;
    oran;
    con2;
    2or;
    ax-r4;
    ax-r2;
    ax-r2;
    con2;
    df-c1;
    comcom5;
  };

  return $|-$ $a C b$;
}
