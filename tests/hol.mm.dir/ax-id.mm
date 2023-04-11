
axiom ax-id(tr: $term$ R) {
  assume ax-id.1: $|- R : bool$;

  return $|-$ $R |= R$;
}
