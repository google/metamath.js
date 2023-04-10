include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "comi31.mm";
include "comid.mm";
include "u3lemc2.mm";
include "comcom.mm";
include "u3lemc4.mm";
include "u3lem1n.mm";
include "ax-r5.mm";
include "ax-a2.mm";
include "ax-r2.mm";

theorem u3lem2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    #;
    wva;
    wi3;
    #;
    wva;
    wi3;
    @1;
    wn;
    #;
    wva;
    wo;
    #;
    wva;
    wva;
    wn;
    #;
    wvb;
    wa;
    @4;
    wvb;
    wn;
    wa;
    wo;
    #;
    wo;
    #;
    @1;
    wva;
    wva;
    @1;
    wva;
    @0;
    wva;
    wva;
    wvb;
    comi31;
    wva;
    comid;
    u3lemc2;
    comcom;
    u3lemc4;
    @3;
    @5;
    wva;
    wo;
    @6;
    @2;
    @5;
    wva;
    wva;
    wvb;
    u3lem1n;
    ax-r5;
    @5;
    wva;
    ax-a2;
    ax-r2;
    ax-r2;
  };

  return $|- ( ( ( a ->3 b ) ->3 a ) ->3 a ) = ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) )$;
}
