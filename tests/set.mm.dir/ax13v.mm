include "ax-13.mm";

theorem ax13v(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {

  disjoint x z;
  disjoint y z;



  do {
    vx;
    vy;
    vz;
    ax-13;
  };

  return $|-$ $( -. x = y -> ( y = z -> A. x y = z ) )$;
}
