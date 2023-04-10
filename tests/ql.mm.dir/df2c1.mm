include "wn.mm";
include "wa.mm";
include "wo.mm";
include "df-a.mm";
include "anor3.mm";
include "2or.mm";
include "ax-r1.mm";
include "ax-r4.mm";
include "ax-r2.mm";
include "con2.mm";
include "df-c1.mm";
include "comcom5.mm";

theorem df2c1(wva: $term$ a, wvb: $term$ b) {
  assume df2c1.1: $|- a = ( ( a v b ) ^ ( a v b ' ) )$;





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
    df2c1.1;
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
    @4;
    @11;
    @2;
    @9;
    @3;
    @10;
    wva;
    wvb;
    anor3;
    wva;
    @1;
    anor3;
    2or;
    ax-r1;
    ax-r4;
    ax-r2;
    ax-r2;
    con2;
    df-c1;
    comcom5;
  };

  return $|- a C b$;
}
