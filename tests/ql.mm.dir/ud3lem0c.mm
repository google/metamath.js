include "ni31.mm";

theorem ud3lem0c(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    ni31;
  };

  return $|-$ $( a ->3 b ) ' = ( ( ( a v b ' ) ^ ( a v b ) ) ^ ( a ' v ( a ^ b ' ) ) )$;
}
