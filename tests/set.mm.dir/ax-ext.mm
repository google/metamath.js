

axiom ax-ext(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {

  return $|-$ $( A. z ( z e. x <-> z e. y ) -> x = y )$;
}
