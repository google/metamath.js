include "ax-6.mm";

theorem ax6v(vx: $setvar$ x, vy: $setvar$ y) {

  disjoint x y;



  do {
    vx;
    vy;
    ax-6;
  };

  return $|-$ $-. A. x -. x = y$;
}
