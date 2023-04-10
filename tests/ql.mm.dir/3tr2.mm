include "ax-r1.mm";
include "3tr1.mm";

theorem 3tr2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume 3tr2.1: $|- a = b$;
  assume 3tr2.2: $|- a = c$;
  assume 3tr2.3: $|- b = d$;





  do {
    wva;
    wvb;
    wvc;
    wvd;
    3tr2.1;
    wva;
    wvc;
    3tr2.2;
    ax-r1;
    wvb;
    wvd;
    3tr2.3;
    ax-r1;
    3tr1;
  };

  return $|-$ $c = d$;
}
