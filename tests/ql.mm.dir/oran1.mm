include "wn.mm";
include "wo.mm";
include "wa.mm";
include "anor2.mm";
include "ax-r1.mm";
include "con3.mm";

theorem oran1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wn;
    wo;
    #;
    wva;
    wn;
    wvb;
    wa;
    #;
    @1;
    @0;
    wn;
    wva;
    wvb;
    anor2;
    ax-r1;
    con3;
  };

  return $|- ( a v b ' ) = ( a ' ^ b ) '$;
}
