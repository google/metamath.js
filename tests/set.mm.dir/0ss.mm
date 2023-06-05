include "c0.mm";
include "cv.mm";
include "wcel.mm";
include "noel.mm";
include "pm2.21i.mm";
include "ssriv.mm";

theorem 0ss(cA: class A) {



  let vx: setvar x;

  do {
    vx;
    c0;
    cA;
    vx;
    cv;
    #;
    c0;
    wcel;
    @0;
    cA;
    wcel;
    @0;
    noel;
    pm2.21i;
    ssriv;
  };

  return |- "(/) C_ A";
}
