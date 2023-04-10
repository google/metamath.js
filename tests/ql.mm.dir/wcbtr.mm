include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wdf-c2.mm";
include "wlan.mm";
include "wr4.mm";
include "w2or.mm";
include "wr2.mm";
include "wdf-c1.mm";

theorem wcbtr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wcbtr.1: $|- C ( a , b ) = 1$;
  assume wcbtr.2: $|- ( b == c ) = 1$;





  do {
    wva;
    wvc;
    wva;
    wva;
    wvb;
    wa;
    #;
    wva;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    wva;
    wvc;
    wa;
    #;
    wva;
    wvc;
    wn;
    #;
    wa;
    #;
    wo;
    wva;
    wvb;
    wcbtr.1;
    wdf-c2;
    @0;
    @3;
    @2;
    @5;
    wvb;
    wvc;
    wva;
    wcbtr.2;
    wlan;
    @1;
    @4;
    wva;
    wvb;
    wvc;
    wcbtr.2;
    wr4;
    wlan;
    w2or;
    wr2;
    wdf-c1;
  };

  return $|-$ $C ( a , c ) = 1$;
}
