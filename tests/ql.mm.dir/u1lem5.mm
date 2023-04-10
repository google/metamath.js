include "wi1.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "df-i1.mm";
include "ancom.mm";
include "u1lemaa.mm";
include "ax-r2.mm";
include "lor.mm";
include "ax-r1.mm";

theorem u1lem5(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wi1;
    #;
    wi1;
    wva;
    wn;
    #;
    wva;
    @0;
    wa;
    #;
    wo;
    #;
    @0;
    wva;
    @0;
    df-i1;
    @3;
    @1;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    @0;
    @2;
    @4;
    @1;
    @2;
    @0;
    wva;
    wa;
    @4;
    wva;
    @0;
    ancom;
    wva;
    wvb;
    u1lemaa;
    ax-r2;
    lor;
    @0;
    @5;
    wva;
    wvb;
    df-i1;
    ax-r1;
    ax-r2;
    ax-r2;
  };

  return $|- ( a ->1 ( a ->1 b ) ) = ( a ->1 b )$;
}
