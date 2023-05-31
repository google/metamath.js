include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wdf-c2.mm";
include "ax-a1.mm";
include "bi1.mm";
include "wlan.mm";
include "wr5-2v.mm";
include "wr2.mm";
include "ax-a2.mm";
include "wdf-c1.mm";

theorem wcomcom2(wva: $term$ a, wvb: $term$ b) {
  assume wcomcom.1: $|- C ( a , b ) = 1$;





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
    #;
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
    wcomcom.1;
    wdf-c2;
    @6;
    @2;
    @3;
    wvb;
    @1;
    wva;
    wvb;
    @1;
    wvb;
    ax-a1;
    bi1;
    wlan;
    wr5-2v;
    wr2;
    @4;
    @5;
    @2;
    @3;
    ax-a2;
    bi1;
    wr2;
    wdf-c1;
  };

  return $|-$ $C ( a , b ' ) = 1$;
}
