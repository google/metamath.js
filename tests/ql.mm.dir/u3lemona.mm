include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "df-i3.mm";
include "ax-r5.mm";
include "or32.mm";
include "lea.mm";
include "lel2or.mm";
include "df-le2.mm";
include "omln.mm";
include "ax-r2.mm";

theorem u3lemona(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    #;
    wva;
    wn;
    #;
    wo;
    @1;
    wvb;
    wa;
    #;
    @1;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wva;
    @1;
    wvb;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    @1;
    wo;
    #;
    @6;
    @0;
    @8;
    @1;
    wva;
    wvb;
    df-i3;
    ax-r5;
    @9;
    @5;
    @1;
    wo;
    #;
    @7;
    wo;
    #;
    @6;
    @5;
    @7;
    @1;
    or32;
    @11;
    @1;
    @7;
    wo;
    @6;
    @10;
    @1;
    @7;
    @5;
    @1;
    @2;
    @1;
    @4;
    @1;
    wvb;
    lea;
    @1;
    @3;
    lea;
    lel2or;
    df-le2;
    ax-r5;
    wva;
    wvb;
    omln;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( ( a ->3 b ) v a ' ) = ( a ' v b )$;
}
