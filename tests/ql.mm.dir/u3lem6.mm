include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "comi31.mm";
include "u3lemc4.mm";
include "u3lem5.mm";
include "lor.mm";
include "ax-a3.mm";
include "ax-r1.mm";
include "oridm.mm";
include "ax-r5.mm";
include "ax-r2.mm";

theorem u3lem6(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wva;
    wvb;
    wi3;
    #;
    wi3;
    #;
    wi3;
    wva;
    wn;
    #;
    @1;
    wo;
    #;
    @1;
    wva;
    @1;
    wva;
    @0;
    comi31;
    u3lemc4;
    @3;
    @2;
    @2;
    wvb;
    wo;
    #;
    wo;
    #;
    @1;
    @1;
    @4;
    @2;
    wva;
    wvb;
    u3lem5;
    #;
    lor;
    @5;
    @2;
    @2;
    wo;
    #;
    wvb;
    wo;
    #;
    @1;
    @8;
    @5;
    @2;
    @2;
    wvb;
    ax-a3;
    ax-r1;
    @8;
    @4;
    @1;
    @7;
    @2;
    wvb;
    @2;
    oridm;
    ax-r5;
    @1;
    @4;
    @6;
    ax-r1;
    ax-r2;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( a ->3 ( a ->3 ( a ->3 b ) ) ) = ( a ->3 ( a ->3 b ) )$;
}
