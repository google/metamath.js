
axiom df-or(vx: $var$ x, vp: $var$ p, vq: $var$ q) {

  return $|- T. |= [ \/ = \ p : bool . \ q : bool . ( ! \ x : bool . [ [ p : bool ==> x : bool ] ==> [ [ q : bool ==> x : bool ] ==> x : bool ] ] ) ]$;
}
