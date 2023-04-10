
axiom ax-wom(wva: $term$ a, wvb: $term$ b) {
  assume ax-wom.1: $|- ( a ' v ( a ^ b ) ) = 1$;

  return $|-$ $( b v ( a ' ^ b ' ) ) = 1$;
}
