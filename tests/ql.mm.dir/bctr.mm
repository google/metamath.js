include "wa.mm";
include "wn.mm";
include "wo.mm";
include "df-c2.mm";
include "ran.mm";
include "2or.mm";
include "3tr1.mm";
include "df-c1.mm";

theorem bctr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume bctr.1: $|- a = b$;
  assume bctr.2: $|- b C c$;





  do {
    wva;
    wvc;
    wvb;
    wvb;
    wvc;
    wa;
    #;
    wvb;
    wvc;
    wn;
    #;
    wa;
    #;
    wo;
    wva;
    wva;
    wvc;
    wa;
    #;
    wva;
    @1;
    wa;
    #;
    wo;
    wvb;
    wvc;
    bctr.2;
    df-c2;
    bctr.1;
    @3;
    @0;
    @4;
    @2;
    wva;
    wvb;
    wvc;
    bctr.1;
    ran;
    wva;
    wvb;
    @1;
    bctr.1;
    ran;
    2or;
    3tr1;
    df-c1;
  };

  return $|- a C c$;
}
