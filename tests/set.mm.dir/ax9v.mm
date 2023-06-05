include "ax-9.mm";

theorem ax9v(vx: setvar x, vy: setvar y, vz: setvar z) {

  disjoint x y;



  do {
    vx;
    vy;
    vz;
    ax-9;
  };

  return |- "( x = y -> ( z e. x -> z e. y ) )";
}
