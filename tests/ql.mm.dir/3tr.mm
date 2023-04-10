include "ax-r2.mm";

theorem 3tr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume 3tr.1: $|- a = b$;
  assume 3tr.2: $|- b = c$;
  assume 3tr.3: $|- c = d$;





  do {
    wva;
    wvc;
    wvd;
    wva;
    wvb;
    wvc;
    3tr.1;
    3tr.2;
    ax-r2;
    3tr.3;
    ax-r2;
  };

  return $|- a = d$;
}
