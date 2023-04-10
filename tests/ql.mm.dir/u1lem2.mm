include "wi1.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wt.mm";
include "df-i1.mm";
include "u1lem1n.mm";
include "u1lem1.mm";
include "ran.mm";
include "anidm.mm";
include "ax-r2.mm";
include "2or.mm";
include "ax-a2.mm";
include "df-t.mm";
include "ax-r1.mm";

theorem u1lem2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    wva;
    wi1;
    #;
    wva;
    wi1;
    @0;
    wn;
    #;
    @0;
    wva;
    wa;
    #;
    wo;
    #;
    wt;
    @0;
    wva;
    df-i1;
    @3;
    wva;
    wn;
    #;
    wva;
    wo;
    #;
    wt;
    @1;
    @4;
    @2;
    wva;
    wva;
    wvb;
    u1lem1n;
    @2;
    wva;
    wva;
    wa;
    wva;
    @0;
    wva;
    wva;
    wva;
    wvb;
    u1lem1;
    ran;
    wva;
    anidm;
    ax-r2;
    2or;
    @5;
    wva;
    @4;
    wo;
    #;
    wt;
    @4;
    wva;
    ax-a2;
    wt;
    @6;
    wva;
    df-t;
    ax-r1;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( ( ( a ->1 b ) ->1 a ) ->1 a ) = 1$;
}
