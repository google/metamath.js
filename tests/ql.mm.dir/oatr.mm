include "wn.mm";
include "wo.mm";
include "wa.mm";
include "leo.mm";
include "wi1.mm";
include "df-i1.mm";
include "ax-a1.mm";
include "ax-r5.mm";
include "ax-r1.mm";
include "ax-r2.mm";
include "lbtr.mm";
include "lel2or.mm";
include "lelan.mm";
include "omlan.mm";
include "lear.mm";
include "letr.mm";

theorem oatr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume oatr.1: $|- b =< ( a ' ->1 c )$;





  do {
    wva;
    wn;
    #;
    wva;
    wvb;
    wo;
    #;
    wa;
    #;
    @0;
    wvc;
    wa;
    #;
    wvc;
    @2;
    @0;
    wva;
    @3;
    wo;
    #;
    wa;
    @3;
    @1;
    @4;
    @0;
    wva;
    @4;
    wvb;
    wva;
    @3;
    leo;
    wvb;
    @0;
    wvc;
    wi1;
    #;
    @4;
    oatr.1;
    @5;
    @0;
    wn;
    #;
    @3;
    wo;
    #;
    @4;
    @0;
    wvc;
    df-i1;
    @4;
    @7;
    wva;
    @6;
    @3;
    wva;
    ax-a1;
    ax-r5;
    ax-r1;
    ax-r2;
    lbtr;
    lel2or;
    lelan;
    wva;
    wvc;
    omlan;
    lbtr;
    @0;
    wvc;
    lear;
    letr;
  };

  return $|- ( a ' ^ ( a v b ) ) =< c$;
}
