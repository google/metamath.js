
axiom ax-distrl(hal: $type$ al, hbe: $type$ be, hga: $type$ ga, vx: $var$ x, vy: $var$ y, ta: $term$ A, tb: $term$ B) {
  assume ax-distrl.1: $|- A : ga$;
  assume ax-distrl.2: $|- B : al$;

  return $|- T. |= ( ( = ( \ x : al . \ y : be . A B ) ) \ y : be . ( \ x : al . A B ) )$;
}
