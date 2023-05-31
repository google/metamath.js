include "cv.mm";
include "wcel.mm";
include "biid.mm";
include "eqriv.mm";

theorem eqid(cA: $class$ A) {



  let vx: $setvar$ x;

  do {
    vx;
    cA;
    cA;
    vx;
    cv;
    cA;
    wcel;
    biid;
    eqriv;
  };

  return $|-$ $A = A$;
}
