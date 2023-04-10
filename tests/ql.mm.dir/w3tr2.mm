include "wr1.mm";
include "w3tr1.mm";

theorem w3tr2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume w3tr2.1: $|- ( a == b ) = 1$;
  assume w3tr2.2: $|- ( a == c ) = 1$;
  assume w3tr2.3: $|- ( b == d ) = 1$;





  do {
    wva;
    wvb;
    wvc;
    wvd;
    w3tr2.1;
    wva;
    wvc;
    w3tr2.2;
    wr1;
    wvb;
    wvd;
    w3tr2.3;
    wr1;
    w3tr1;
  };

  return $|- ( c == d ) = 1$;
}
