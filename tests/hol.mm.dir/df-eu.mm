
axiom df-eu(hal: $type$ al, vx: $var$ x, vy: $var$ y, vp: $var$ p) {

  return $|- T. |= [ ?! = \ p : ( al -> bool ) . ( ? \ y : al . ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) = [ x : al = y : al ] ] ) ) ]$;
}
