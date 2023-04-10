
axiom ax-r2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume r2.1: $|- a = b$;
  assume r2.2: $|- b = c$;

  return $|- a = c$;
}
