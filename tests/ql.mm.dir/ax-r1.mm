
axiom ax-r1(wva: $term$ a, wvb: $term$ b) {
  assume r1.1: $|- a = b$;

  return $|- b = a$;
}
