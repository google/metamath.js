include "li3.mm";

theorem ud3lem0a(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume ud3lem0a.1: $|- a = b$;





  do {
    wva;
    wvb;
    wvc;
    ud3lem0a.1;
    li3;
  };

  return $|-$ $( c ->3 a ) = ( c ->3 b )$;
}
