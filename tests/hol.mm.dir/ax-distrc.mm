
axiom ax-distrc(hal: $type$ al, hbe: $type$ be, hga: $type$ ga, vx: $var$ x, ta: $term$ A, tb: $term$ B, tf: $term$ F) {
  assume ax-beta.1: $|- A : be$;
  assume ax-distrc.2: $|- B : al$;
  assume ax-distrc.3: $|- F : ( be -> ga )$;

  return $|-$ $T. |= ( ( = ( \ x : al . ( F A ) B ) ) ( ( \ x : al . F B ) ( \ x : al . A B ) ) )$;
}
