include "axext3.mm";
include "df-cleq.mm";

theorem dfcleq(vx: 'setvar' x, cA: 'class' A, cB: 'class' B) {

  disjoint A x;
  disjoint B x;
  disjoint x y;
  disjoint x z;
  disjoint y z;

  let vy: setvar y;
  let vz: setvar z;

  do {
    vx;
    vy;
    vz;
    cA;
    cB;
    vy;
    vz;
    vx;
    axext3;
    df-cleq;
  };

  return '|-' "( A = B <-> A. x ( x e. A <-> x e. B ) )";
}
