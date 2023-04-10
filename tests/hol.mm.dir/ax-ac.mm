
axiom ax-ac(hal: $type$ al, vx: $var$ x, vp: $var$ p) {

  return $|- T. |= ( ! \ p : ( al -> bool ) . ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) ==> ( p : ( al -> bool ) ( @ p : ( al -> bool ) ) ) ] ) )$;
}
