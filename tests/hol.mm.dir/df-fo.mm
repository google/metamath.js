
axiom df-fo(hal: $type$ al, hbe: $type$ be, vx: $var$ x, vy: $var$ y, vf: $var$ f) {

  return $|- T. |= [ onto = \ f : ( al -> be ) . ( ! \ y : be . ( ? \ x : al . [ y : be = ( f : ( al -> be ) x : al ) ] ) ) ]$;
}
