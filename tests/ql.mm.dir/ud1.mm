include "wi1.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "ud1lem1.mm";
include "ud1lem0b.mm";
include "ud1lem2.mm";
include "ax-r2.mm";
include "ud1lem0a.mm";
include "ud1lem3.mm";
include "ax-r1.mm";

theorem ud1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    #;
    @0;
    wvb;
    wva;
    wi1;
    wi1;
    #;
    wva;
    wi1;
    #;
    wi1;
    #;
    wva;
    wvb;
    wo;
    #;
    @3;
    @0;
    @4;
    wi1;
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
    wi1;
    @4;
    @1;
    @5;
    wva;
    wva;
    wvb;
    ud1lem1;
    ud1lem0b;
    wva;
    wvb;
    ud1lem2;
    ax-r2;
    ud1lem0a;
    wva;
    wvb;
    ud1lem3;
    ax-r2;
    ax-r1;
  };

  return $|- ( a v b ) = ( ( a ->1 b ) ->1 ( ( ( a ->1 b ) ->1 ( b ->1 a ) ) ->1 a ) )$;
}
