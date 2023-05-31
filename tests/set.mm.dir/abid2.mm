include "cv.mm";
include "wcel.mm";
include "cab.mm";
include "abid1.mm";
include "eqcomi.mm";

theorem abid2(vx: $setvar$ x, cA: $class$ A) {

  disjoint A x;



  do {
    cA;
    vx;
    cv;
    cA;
    wcel;
    vx;
    cab;
    vx;
    cA;
    abid1;
    eqcomi;
  };

  return $|-$ ${ x | x e. A } = A$;
}
