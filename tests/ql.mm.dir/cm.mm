include "ax-r1.mm";

theorem cm(wva: $term$ a, wvb: $term$ b) {
  assume cm.1: $|- a = b$;





  do {
    wva;
    wvb;
    cm.1;
    ax-r1;
  };

  return $|-$ $b = a$;
}
