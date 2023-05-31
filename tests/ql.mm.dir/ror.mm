include "ax-r5.mm";

theorem ror(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume lor.1: $|- a = b$;





  do {
    wva;
    wvb;
    wvc;
    lor.1;
    ax-r5;
  };

  return $|-$ $( a v c ) = ( b v c )$;
}
