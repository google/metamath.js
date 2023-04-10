include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "comi31.mm";
include "u3lemc4.mm";
include "ax-a2.mm";
include "u3lemona.mm";
include "ax-r2.mm";

theorem u3lem5(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wi3;
    #;
    wi3;
    wva;
    wn;
    #;
    @0;
    wo;
    #;
    @1;
    wvb;
    wo;
    #;
    wva;
    @0;
    wva;
    wvb;
    comi31;
    u3lemc4;
    @2;
    @0;
    @1;
    wo;
    @3;
    @1;
    @0;
    ax-a2;
    wva;
    wvb;
    u3lemona;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( a ->3 ( a ->3 b ) ) = ( a ' v b )$;
}
