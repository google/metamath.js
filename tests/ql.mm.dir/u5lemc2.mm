include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wi5.mm";
include "com2an.mm";
include "comcom2.mm";
include "com2or.mm";
include "df-i5.mm";
include "ax-r1.mm";
include "cbtr.mm";

theorem u5lemc2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume ulemc2.1: $|- a C b$;
  assume ulemc2.2: $|- a C c$;





  do {
    wva;
    wvb;
    wvc;
    wa;
    #;
    wvb;
    wn;
    #;
    wvc;
    wa;
    #;
    wo;
    #;
    @1;
    wvc;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wvb;
    wvc;
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
    wvc;
    ulemc2.1;
    ulemc2.2;
    com2an;
    wva;
    @1;
    wvc;
    wva;
    wvb;
    ulemc2.1;
    comcom2;
    #;
    ulemc2.2;
    com2an;
    com2or;
    wva;
    @1;
    @4;
    @8;
    wva;
    wvc;
    ulemc2.2;
    comcom2;
    com2an;
    com2or;
    @7;
    @6;
    wvb;
    wvc;
    df-i5;
    ax-r1;
    cbtr;
  };

  return $|-$ $a C ( b ->5 c )$;
}
