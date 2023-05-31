include "tb.mm";
include "wn.mm";
include "conb.mm";
include "bi1.mm";

theorem wcon(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    tb;
    wva;
    wn;
    wvb;
    wn;
    tb;
    wva;
    wvb;
    conb;
    bi1;
  };

  return $|-$ $( ( a == b ) == ( a ' == b ' ) ) = 1$;
}
