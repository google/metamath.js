
axiom ax-r4(wva: $term$ a, wvb: $term$ b) {
  assume r4.1: $|- a = b$;

  return $|- a ' = b '$;
}
