include "wo.mm";
include "ax-r5.mm";
include "ax-a2.mm";
include "3tr1.mm";

theorem lor(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume lor.1: $|- a = b$;





  do {
    wva;
    wvc;
    wo;
    wvb;
    wvc;
    wo;
    wvc;
    wva;
    wo;
    wvc;
    wvb;
    wo;
    wva;
    wvb;
    wvc;
    lor.1;
    ax-r5;
    wvc;
    wva;
    ax-a2;
    wvc;
    wvb;
    ax-a2;
    3tr1;
  };

  return $|- ( c v a ) = ( c v b )$;
}
