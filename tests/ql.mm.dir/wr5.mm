include "wr5-2v.mm";

theorem wr5(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wr5.1: $|- ( a == b ) = 1$;





  do {
    wva;
    wvb;
    wvc;
    wr5.1;
    wr5-2v;
  };

  return $|-$ $( ( a v c ) == ( b v c ) ) = 1$;
}
