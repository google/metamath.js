include "wn.mm";
include "wi3.mm";
include "wo.mm";
include "comi31.mm";
include "u3lemc4.mm";
include "wa.mm";
include "u3lem7.mm";
include "lor.mm";
include "ax-a3.mm";
include "ax-r1.mm";
include "oridm.mm";
include "ax-r5.mm";
include "ax-r2.mm";

theorem u3lem9(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wva;
    wn;
    #;
    wvb;
    wi3;
    #;
    wi3;
    #;
    wi3;
    @0;
    @2;
    wo;
    #;
    @2;
    wva;
    @2;
    wva;
    @1;
    comi31;
    u3lemc4;
    @3;
    @0;
    @0;
    wva;
    wvb;
    wa;
    wva;
    wvb;
    wn;
    wa;
    wo;
    #;
    wo;
    #;
    wo;
    #;
    @2;
    @2;
    @5;
    @0;
    wva;
    wvb;
    u3lem7;
    #;
    lor;
    @6;
    @0;
    @0;
    wo;
    #;
    @4;
    wo;
    #;
    @2;
    @9;
    @6;
    @0;
    @0;
    @4;
    ax-a3;
    ax-r1;
    @9;
    @5;
    @2;
    @8;
    @0;
    @4;
    @0;
    oridm;
    ax-r5;
    @2;
    @5;
    @7;
    ax-r1;
    ax-r2;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|- ( a ->3 ( a ->3 ( a ' ->3 b ) ) ) = ( a ->3 ( a ' ->3 b ) )$;
}
