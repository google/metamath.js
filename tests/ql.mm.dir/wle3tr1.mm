include "wbltr.mm";
include "wr1.mm";
include "wlbtr.mm";

theorem wle3tr1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume wle3tr1.1: $|- ( a =<2 b ) = 1$;
  assume wle3tr1.2: $|- ( c == a ) = 1$;
  assume wle3tr1.3: $|- ( d == b ) = 1$;





  do {
    wvc;
    wvb;
    wvd;
    wvc;
    wva;
    wvb;
    wle3tr1.2;
    wle3tr1.1;
    wbltr;
    wvd;
    wvb;
    wle3tr1.3;
    wr1;
    wlbtr;
  };

  return $|-$ $( c =<2 d ) = 1$;
}
