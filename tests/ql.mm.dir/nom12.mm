include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wi2.mm";
include "wi1.mm";
include "oran.mm";
include "ax-r1.mm";
include "orabs.mm";
include "ax-r2.mm";
include "con3.mm";
include "lor.mm";
include "ax-a2.mm";
include "df-i2.mm";
include "df-i1.mm";
include "3tr1.mm";

theorem nom12(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wn;
    #;
    @0;
    wn;
    wa;
    #;
    wo;
    #;
    @1;
    @0;
    wo;
    #;
    wva;
    @0;
    wi2;
    wva;
    wvb;
    wi1;
    @3;
    @0;
    @1;
    wo;
    @4;
    @2;
    @1;
    @0;
    @2;
    wva;
    @2;
    wn;
    #;
    wva;
    @0;
    wo;
    #;
    wva;
    @6;
    @5;
    wva;
    @0;
    oran;
    ax-r1;
    wva;
    wvb;
    orabs;
    ax-r2;
    con3;
    lor;
    @0;
    @1;
    ax-a2;
    ax-r2;
    wva;
    @0;
    df-i2;
    wva;
    wvb;
    df-i1;
    3tr1;
  };

  return $|- ( a ->2 ( a ^ b ) ) = ( a ->1 b )$;
}
