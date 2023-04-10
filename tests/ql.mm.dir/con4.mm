include "ax-r4.mm";

theorem con4(wva: $term$ a, wvb: $term$ b) {
  assume con4.1: $|- a = b$;





  do {
    wva;
    wvb;
    con4.1;
    ax-r4;
  };

  return $|- a ' = b '$;
}
