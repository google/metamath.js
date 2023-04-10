
axiom df-le2(wva: $term$ a, wvb: $term$ b) {
  assume df-le2.1: $|- a =< b$;

  return $|-$ $( a v b ) = b$;
}
