include "wn.mm";
include "wa.mm";
include "wo.mm";
include "oran.mm";
include "ax-r1.mm";
include "con3.mm";

theorem anor3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    wvb;
    wn;
    wa;
    #;
    wva;
    wvb;
    wo;
    #;
    @1;
    @0;
    wn;
    wva;
    wvb;
    oran;
    ax-r1;
    con3;
  };

  return $|-$ $( a ' ^ b ' ) = ( a v b ) '$;
}
