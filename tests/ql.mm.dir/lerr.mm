include "wo.mm";
include "ler.mm";
include "ax-a2.mm";
include "lbtr.mm";

theorem lerr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume le.1: $|- a =< b$;





  do {
    wva;
    wvb;
    wvc;
    wo;
    wvc;
    wvb;
    wo;
    wva;
    wvb;
    wvc;
    le.1;
    ler;
    wvb;
    wvc;
    ax-a2;
    lbtr;
  };

  return $|-$ $a =< ( c v b )$;
}
