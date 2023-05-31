
axiom df-le1(wva: $term$ a, wvb: $term$ b) {
  assume df-le1.1: $|- ( a v b ) = b$;

  return $|-$ $a =< b$;
}
