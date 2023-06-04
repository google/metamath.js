include "ax7v.mm";

theorem ax7v1(vx: 'setvar' x, vy: 'setvar' y, vz: 'setvar' z) {

  disjoint x y;
  disjoint x z;



  do {
    vx;
    vy;
    vz;
    ax7v;
  };

  return '|-' "( x = y -> ( x = z -> y = z ) )";
}
