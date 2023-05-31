include "wi5.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "u5lemc1b.mm";
include "comcom.mm";
include "u5lemc4.mm";
include "u5lem1n.mm";
include "ax-r5.mm";
include "ax-a2.mm";
include "ax-r2.mm";

theorem u5lem2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi5;
    #;
    wva;
    wi5;
    #;
    wva;
    wi5;
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
    @0;
    wva;
    u5lemc1b;
    comcom;
    u5lemc4;
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
    u5lem1n;
    ax-r5;
    @5;
    wva;
    ax-a2;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( ( ( a ->5 b ) ->5 a ) ->5 a ) = ( a v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) )$;
}
