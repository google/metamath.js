
axiom ax-eta(hal: $type$ al, hbe: $type$ be, vx: $var$ x, vf: $var$ f) {

  return $|- T. |= ( ! \ f : ( al -> be ) . [ \ x : al . ( f : ( al -> be ) x : al ) = f : ( al -> be ) ] )$;
}
