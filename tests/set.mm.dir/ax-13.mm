

axiom ax-13(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {

  return $|-$ $( -. x = y -> ( y = z -> A. x y = z ) )$;
}
