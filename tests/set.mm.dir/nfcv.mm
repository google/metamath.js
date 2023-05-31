include "cv.mm";
include "wcel.mm";
include "nfv.mm";
include "nfci.mm";

theorem nfcv(vx: $setvar$ x, cA: $class$ A) {

  disjoint A x;
  disjoint x y;
  disjoint A y;

  let vy: $setvar$ y;

  do {
    vx;
    vy;
    cA;
    vy;
    cv;
    cA;
    wcel;
    vx;
    nfv;
    nfci;
  };

  return $|-$ $F/_ x A$;
}
