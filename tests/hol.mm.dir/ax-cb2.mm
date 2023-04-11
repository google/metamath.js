
axiom ax-cb2(ta: $term$ A, tr: $term$ R) {
  assume ax-cb.1: $|- R |= A$;

  return $|-$ $A : bool$;
}
