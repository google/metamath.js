include "wi3.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "df-i3.mm";
include "ax-r5.mm";
include "ax-a3.mm";
include "lea.mm";
include "df-le2.mm";
include "lor.mm";
include "ax-a2.mm";
include "ax-r2.mm";

theorem u3lemoa(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    #;
    wva;
    wo;
    wva;
    wn;
    #;
    wvb;
    wa;
    @1;
    wvb;
    wn;
    wa;
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
    wva;
    wo;
    #;
    wva;
    @2;
    wo;
    #;
    @0;
    @5;
    wva;
    wva;
    wvb;
    df-i3;
    ax-r5;
    @6;
    @2;
    @4;
    wva;
    wo;
    #;
    wo;
    #;
    @7;
    @2;
    @4;
    wva;
    ax-a3;
    @9;
    @2;
    wva;
    wo;
    @7;
    @8;
    wva;
    @2;
    @4;
    wva;
    wva;
    @3;
    lea;
    df-le2;
    lor;
    @2;
    wva;
    ax-a2;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( ( a ->3 b ) v a ) = ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) )$;
}
