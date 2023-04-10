
axiom df-f11(hal: $type$ al, hbe: $type$ be, vx: $var$ x, vy: $var$ y, vf: $var$ f) {

  return $|- T. |= [ 1-1 = \ f : ( al -> be ) . ( ! \ x : al . ( ! \ y : al . [ [ ( f : ( al -> be ) x : al ) = ( f : ( al -> be ) y : al ) ] ==> [ x : al = y : al ] ] ) ) ]$;
}
