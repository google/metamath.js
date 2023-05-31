include "tb.mm";
include "wn.mm";
include "bicom.mm";
include "conb.mm";
include "ax-r2.mm";

theorem nomcon5(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    tb;
    wvb;
    wva;
    tb;
    wvb;
    wn;
    wva;
    wn;
    tb;
    wva;
    wvb;
    bicom;
    wvb;
    wva;
    conb;
    ax-r2;
  };

  return $|-$ $( a == b ) = ( b ' == a ' )$;
}
