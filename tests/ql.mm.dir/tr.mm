include "ax-r2.mm";

theorem tr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume tr.1: $|- a = b$;
  assume tr.2: $|- b = c$;





  do {
    wva;
    wvb;
    wvc;
    tr.1;
    tr.2;
    ax-r2;
  };

  return $|- a = c$;
}
