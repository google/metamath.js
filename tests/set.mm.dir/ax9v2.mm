include "ax9v.mm";

theorem ax9v2(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {

  disjoint x y;
  disjoint y z;



  do {
    vx;
    vy;
    vz;
    ax9v;
  };

  return $|-$ $( x = y -> ( z e. x -> z e. y ) )$;
}
