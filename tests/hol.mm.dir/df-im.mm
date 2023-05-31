
axiom df-im(vp: $var$ p, vq: $var$ q) {

  return $|-$ $T. |= [ ==> = \ p : bool . \ q : bool . [ [ p : bool /\ q : bool ] = p : bool ] ]$;
}
