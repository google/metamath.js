include "wi3.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "ud3lem1.mm";
include "ud3lem0b.mm";
include "ud3lem2.mm";
include "ax-r2.mm";
include "ud3lem0a.mm";
include "ud3lem3.mm";
include "ax-r1.mm";

theorem ud3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    #;
    @0;
    wvb;
    wva;
    wi3;
    wi3;
    #;
    wva;
    wi3;
    #;
    wi3;
    #;
    wva;
    wvb;
    wo;
    #;
    @3;
    @0;
    @4;
    wi3;
    @4;
    @2;
    @4;
    @0;
    @2;
    wva;
    wva;
    wn;
    wvb;
    wn;
    wa;
    wo;
    #;
    wva;
    wi3;
    @4;
    @1;
    @5;
    wva;
    wva;
    wvb;
    ud3lem1;
    ud3lem0b;
    wva;
    wvb;
    ud3lem2;
    ax-r2;
    ud3lem0a;
    wva;
    wvb;
    ud3lem3;
    ax-r2;
    ax-r1;
  };

  return $|- ( a v b ) = ( ( a ->3 b ) ->3 ( ( ( a ->3 b ) ->3 ( b ->3 a ) ) ->3 a ) )$;
}
