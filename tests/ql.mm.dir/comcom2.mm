include "wn.mm";
include "wa.mm";
include "wo.mm";
include "df-c2.mm";
include "ax-a1.mm";
include "lan.mm";
include "ax-r5.mm";
include "ax-r2.mm";
include "ax-a2.mm";
include "df-c1.mm";

theorem comcom2(wva: $term$ a, wvb: $term$ b) {
  assume comcom2.1: $|- a C b$;





  do {
    wva;
    wvb;
    wn;
    #;
    wva;
    wva;
    @0;
    wn;
    #;
    wa;
    #;
    wva;
    @0;
    wa;
    #;
    wo;
    #;
    @3;
    @2;
    wo;
    wva;
    wva;
    wvb;
    wa;
    #;
    @3;
    wo;
    @4;
    wva;
    wvb;
    comcom2.1;
    df-c2;
    @5;
    @2;
    @3;
    wvb;
    @1;
    wva;
    wvb;
    ax-a1;
    lan;
    ax-r5;
    ax-r2;
    @2;
    @3;
    ax-a2;
    ax-r2;
    df-c1;
  };

  return $|-$ $a C b '$;
}
