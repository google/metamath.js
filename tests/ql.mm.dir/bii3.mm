include "tb.mm";
include "wi3.mm";
include "wa.mm";
include "i3bi.mm";
include "ax-r1.mm";
include "lea.mm";
include "bltr.mm";
include "lei3.mm";

theorem bii3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    tb;
    #;
    wva;
    wvb;
    wi3;
    #;
    @0;
    @1;
    wvb;
    wva;
    wi3;
    #;
    wa;
    #;
    @1;
    @3;
    @0;
    wva;
    wvb;
    i3bi;
    ax-r1;
    @1;
    @2;
    lea;
    bltr;
    lei3;
  };

  return $|-$ $( ( a == b ) ->3 ( a ->3 b ) ) = 1$;
}
