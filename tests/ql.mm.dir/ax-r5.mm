
axiom ax-r5(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume r5.1: $|- a = b$;

  return $|- ( a v c ) = ( b v c )$;
}
