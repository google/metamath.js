

axiom ax-cb1(ta: $term$ A, tr: $term$ R) {
  assume ax-cb.1: $|- R |= A$;

  return $|-$ $R : bool$;
}
