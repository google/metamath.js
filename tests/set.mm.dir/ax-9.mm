

axiom ax-9(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {

  return $|-$ $( x = y -> ( z e. x -> z e. y ) )$;
}
