include "wa.mm";
include "wi1.mm";
include "wn.mm";
include "wo.mm";
include "leo.mm";
include "wi3.mm";
include "ran.mm";
include "u3lemab.mm";
include "3tr2.mm";
include "u1lemab.mm";
include "ax-r1.mm";
include "ax-r2.mm";
include "lbtr.mm";
include "lea.mm";
include "letr.mm";

theorem neg3antlem1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume neg3ant.1: $|- ( a ->3 c ) = ( b ->3 c )$;





  do {
    wva;
    wvc;
    wa;
    #;
    wvb;
    wvc;
    wi1;
    #;
    wvc;
    wa;
    #;
    @1;
    @0;
    @0;
    wva;
    wn;
    wvc;
    wa;
    #;
    wo;
    #;
    @2;
    @0;
    @3;
    leo;
    @4;
    wvb;
    wvc;
    wa;
    wvb;
    wn;
    wvc;
    wa;
    wo;
    #;
    @2;
    wva;
    wvc;
    wi3;
    #;
    wvc;
    wa;
    wvb;
    wvc;
    wi3;
    #;
    wvc;
    wa;
    @4;
    @5;
    @6;
    @7;
    wvc;
    neg3ant.1;
    ran;
    wva;
    wvc;
    u3lemab;
    wvb;
    wvc;
    u3lemab;
    3tr2;
    @2;
    @5;
    wvb;
    wvc;
    u1lemab;
    ax-r1;
    ax-r2;
    lbtr;
    @1;
    wvc;
    lea;
    letr;
  };

  return $|- ( a ^ c ) =< ( b ->1 c )$;
}
