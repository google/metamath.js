include "wi3.mm";
include "ri3.mm";
include "bi1.mm";
include "wwbmpr.mm";

theorem bi3tr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume bi3tr.1: $|- a = b$;
  assume bi3tr.2: $|- ( b ->3 c ) = 1$;





  do {
    wva;
    wvc;
    wi3;
    #;
    wvb;
    wvc;
    wi3;
    #;
    bi3tr.2;
    @0;
    @1;
    wva;
    wvb;
    wvc;
    bi3tr.1;
    ri3;
    bi1;
    wwbmpr;
  };

  return $|-$ $( a ->3 c ) = 1$;
}
