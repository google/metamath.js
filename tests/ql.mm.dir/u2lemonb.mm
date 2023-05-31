include "wi2.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "wt.mm";
include "df-i2.mm";
include "ax-r5.mm";
include "or32.mm";
include "ax-a2.mm";
include "df-t.mm";
include "lor.mm";
include "ax-r1.mm";
include "or1.mm";
include "ax-r2.mm";

theorem u2lemonb(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi2;
    #;
    wvb;
    wn;
    #;
    wo;
    wvb;
    wva;
    wn;
    @1;
    wa;
    #;
    wo;
    #;
    @1;
    wo;
    #;
    wt;
    @0;
    @3;
    @1;
    wva;
    wvb;
    df-i2;
    ax-r5;
    @4;
    wvb;
    @1;
    wo;
    #;
    @2;
    wo;
    #;
    wt;
    wvb;
    @2;
    @1;
    or32;
    @6;
    @2;
    @5;
    wo;
    #;
    wt;
    @5;
    @2;
    ax-a2;
    @7;
    @2;
    wt;
    wo;
    #;
    wt;
    @8;
    @7;
    wt;
    @5;
    @2;
    wvb;
    df-t;
    lor;
    ax-r1;
    @2;
    or1;
    ax-r2;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( ( a ->2 b ) v b ' ) = 1$;
}
