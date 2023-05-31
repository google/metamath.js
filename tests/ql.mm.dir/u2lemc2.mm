include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wi2.mm";
include "comcom2.mm";
include "com2an.mm";
include "com2or.mm";
include "df-i2.mm";
include "ax-r1.mm";
include "cbtr.mm";

theorem u2lemc2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume ulemc2.1: $|- a C b$;
  assume ulemc2.2: $|- a C c$;





  do {
    wva;
    wvc;
    wvb;
    wn;
    #;
    wvc;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wvb;
    wvc;
    wi2;
    #;
    wva;
    wvc;
    @2;
    ulemc2.2;
    wva;
    @0;
    @1;
    wva;
    wvb;
    ulemc2.1;
    comcom2;
    wva;
    wvc;
    ulemc2.2;
    comcom2;
    com2an;
    com2or;
    @4;
    @3;
    wvb;
    wvc;
    df-i2;
    ax-r1;
    cbtr;
  };

  return $|-$ $a C ( b ->2 c )$;
}
