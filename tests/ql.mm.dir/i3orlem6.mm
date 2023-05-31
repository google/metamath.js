include "wa.mm";
include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "ax-a3.mm";
include "ax-r1.mm";
include "i3orlem2.mm";
include "lerr.mm";
include "df-le2.mm";
include "oi3ai3.mm";
include "ax-r5.mm";
include "3tr2.mm";

theorem i3orlem6(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wvb;
    wi3;
    wn;
    #;
    wva;
    wvc;
    wo;
    wvb;
    wvc;
    wo;
    wi3;
    #;
    wo;
    #;
    wo;
    #;
    @0;
    @1;
    wo;
    #;
    @2;
    wo;
    #;
    @3;
    wva;
    wvb;
    wo;
    wva;
    wn;
    wvb;
    wn;
    wi3;
    wa;
    #;
    @2;
    wo;
    @6;
    @4;
    @0;
    @1;
    @2;
    ax-a3;
    ax-r1;
    @0;
    @3;
    @0;
    @2;
    @1;
    wva;
    wvb;
    wvc;
    i3orlem2;
    lerr;
    df-le2;
    @5;
    @7;
    @2;
    wva;
    wvb;
    oi3ai3;
    ax-r5;
    3tr2;
  };

  return $|-$ $( ( a ->3 b ) ' v ( ( a v c ) ->3 ( b v c ) ) ) = ( ( ( a v b ) ^ ( a ' ->3 b ' ) ) v ( ( a v c ) ->3 ( b v c ) ) )$;
}
