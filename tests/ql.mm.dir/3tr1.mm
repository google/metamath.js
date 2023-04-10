include "ax-r1.mm";
include "ax-r2.mm";

theorem 3tr1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume 3tr1.1: $|- a = b$;
  assume 3tr1.2: $|- c = a$;
  assume 3tr1.3: $|- d = b$;





  do {
    wvc;
    wva;
    wvd;
    3tr1.2;
    wva;
    wvb;
    wvd;
    3tr1.1;
    wvd;
    wvb;
    3tr1.3;
    ax-r1;
    ax-r2;
    ax-r2;
  };

  return $|- c = d$;
}
