include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wi1.mm";
include "comcom2.mm";
include "com2an.mm";
include "com2or.mm";
include "df-i1.mm";
include "ax-r1.mm";
include "cbtr.mm";

theorem u1lemc2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume ulemc2.1: $|- a C b$;
  assume ulemc2.2: $|- a C c$;





  do {
    wva;
    wvb;
    wn;
    #;
    wvb;
    wvc;
    wa;
    #;
    wo;
    #;
    wvb;
    wvc;
    wi1;
    #;
    wva;
    @0;
    @1;
    wva;
    wvb;
    ulemc2.1;
    comcom2;
    wva;
    wvb;
    wvc;
    ulemc2.1;
    ulemc2.2;
    com2an;
    com2or;
    @3;
    @2;
    wvb;
    wvc;
    df-i1;
    ax-r1;
    cbtr;
  };

  return $|- a C ( b ->1 c )$;
}
