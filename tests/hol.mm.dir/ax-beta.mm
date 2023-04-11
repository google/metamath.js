

axiom ax-beta(hal: $type$ al, hbe: $type$ be, vx: $var$ x, ta: $term$ A) {
  assume ax-beta.1: $|- A : be$;

  return $|-$ $T. |= ( ( = ( \ x : al . A x : al ) ) A )$;
}
