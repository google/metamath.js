include "wo.mm";
include "wa.mm";
include "ml3le.mm";
include "lebi.mm";

theorem ml3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    wva;
    wo;
    wa;
    wo;
    wva;
    wvc;
    wvb;
    wva;
    wo;
    wa;
    wo;
    wva;
    wvb;
    wvc;
    ml3le;
    wva;
    wvc;
    wvb;
    ml3le;
    lebi;
  };

  return $|-$ $( a v ( b ^ ( c v a ) ) ) = ( a v ( c ^ ( b v a ) ) )$;
}
