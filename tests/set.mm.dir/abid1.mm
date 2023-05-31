include "cv.mm";
include "wcel.mm";
include "biid.mm";
include "abbi2i.mm";

theorem abid1(vx: $setvar$ x, cA: $class$ A) {

  disjoint A x;



  do {
    vx;
    cv;
    cA;
    wcel;
    #;
    vx;
    cA;
    @0;
    biid;
    abbi2i;
  };

  return $|-$ $A = { x | x e. A }$;
}
