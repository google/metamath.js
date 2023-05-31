

axiom df-ov(hal: $type$ al, hbe: $type$ be, hga: $type$ ga, ta: $term$ A, tb: $term$ B, tf: $term$ F) {
  assume wov.1: $|- F : ( al -> ( be -> ga ) )$;
  assume wov.2: $|- A : al$;
  assume wov.3: $|- B : be$;

  return $|-$ $T. |= ( ( = [ A F B ] ) ( ( F A ) B ) )$;
}
