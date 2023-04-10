

axiom df-al(hal: $type$ al, vx: $var$ x, vp: $var$ p) {

  return $|- T. |= [ ! = \ p : ( al -> bool ) . [ p : ( al -> bool ) = \ x : al . T. ] ]$;
}
