
axiom df-ex(hal: $type$ al, vx: $var$ x, vp: $var$ p, vq: $var$ q) {

  return $|- T. |= [ ? = \ p : ( al -> bool ) . ( ! \ q : bool . [ ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) ==> q : bool ] ) ==> q : bool ] ) ]$;
}
