include "ri3.mm";

theorem ud3lem0b(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume ud3lem0a.1: $|- a = b$;





  do {
    wva;
    wvb;
    wvc;
    ud3lem0a.1;
    ri3;
  };

  return $|-$ $( a ->3 c ) = ( b ->3 c )$;
}
