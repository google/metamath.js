include "wn.mm";
include "wi1.mm";
include "wa.mm";
include "wo.mm";
include "oran3.mm";
include "ax-r1.mm";
include "u1lem9ab.mm";
include "le2or.mm";
include "lecom.mm";
include "bctr.mm";
include "comcom6.mm";
include "comcom.mm";

theorem 3vcom(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wn;
    wvc;
    wi1;
    #;
    wvb;
    wn;
    wvc;
    wi1;
    #;
    wa;
    #;
    wva;
    wvc;
    wi1;
    #;
    wvb;
    wvc;
    wi1;
    #;
    wo;
    #;
    @2;
    @5;
    @2;
    wn;
    #;
    @0;
    wn;
    #;
    @1;
    wn;
    #;
    wo;
    #;
    @5;
    @9;
    @6;
    @0;
    @1;
    oran3;
    ax-r1;
    @9;
    @5;
    @7;
    @3;
    @8;
    @4;
    wva;
    wvc;
    u1lem9ab;
    wvb;
    wvc;
    u1lem9ab;
    le2or;
    lecom;
    bctr;
    comcom6;
    comcom;
  };

  return $|- ( ( a ->1 c ) v ( b ->1 c ) ) C ( ( a ' ->1 c ) ^ ( b ' ->1 c ) )$;
}
