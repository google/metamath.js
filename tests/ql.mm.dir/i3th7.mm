include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "leor.mm";
include "lem4.mm";
include "ax-r1.mm";
include "i3abs3.mm";
include "ax-r2.mm";
include "lbtr.mm";
include "lei3.mm";

theorem i3th7(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wi3;
    #;
    wva;
    wi3;
    #;
    wva;
    @0;
    wn;
    #;
    wva;
    wo;
    #;
    @1;
    wva;
    @2;
    leor;
    @3;
    @0;
    @1;
    wi3;
    #;
    @1;
    @4;
    @3;
    @0;
    wva;
    lem4;
    ax-r1;
    wva;
    wvb;
    i3abs3;
    ax-r2;
    lbtr;
    lei3;
  };

  return $|-$ $( a ->3 ( ( a ->3 b ) ->3 a ) ) = 1$;
}
