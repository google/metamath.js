include "ax-7.mm";

theorem ax7v(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {

  disjoint x y;



  do {
    vx;
    vy;
    vz;
    ax-7;
  };

  return $|-$ $( x = y -> ( x = z -> y = z ) )$;
}
