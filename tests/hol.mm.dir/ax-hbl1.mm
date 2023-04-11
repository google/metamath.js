
axiom ax-hbl1(hal: $type$ al, hbe: $type$ be, hga: $type$ ga, vx: $var$ x, ta: $term$ A, tb: $term$ B) {
  assume ax-hbl1.1: $|- A : ga$;
  assume ax-hbl1.2: $|- B : al$;

  return $|-$ $T. |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ]$;
}
