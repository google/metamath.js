include "cv.mm";
include "wceq.mm";

theorem weq(vx: setvar x, vy: setvar y) {





  do {
    vx;
    cv;
    vy;
    cv;
    wceq;
  };

  return wff "x = y";
}
