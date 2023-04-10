include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wi5.mm";
include "comanr1.mm";
include "comcom6.mm";
include "com2or.mm";
include "df-i5.mm";
include "ax-r1.mm";
include "cbtr.mm";

theorem u5lemc1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wa;
    #;
    wva;
    wn;
    #;
    wvb;
    wa;
    #;
    wo;
    #;
    @1;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wva;
    wvb;
    wi5;
    #;
    wva;
    @3;
    @5;
    wva;
    @0;
    @2;
    wva;
    wvb;
    comanr1;
    wva;
    @2;
    @1;
    wvb;
    comanr1;
    comcom6;
    com2or;
    wva;
    @5;
    @1;
    @4;
    comanr1;
    comcom6;
    com2or;
    @7;
    @6;
    wva;
    wvb;
    df-i5;
    ax-r1;
    cbtr;
  };

  return $|- a C ( a ->5 b )$;
}
