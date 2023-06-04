include "cv.mm";
include "wcel.mm";

theorem wel(vx: 'setvar' x, vy: 'setvar' y) {





  do {
    vx;
    cv;
    vy;
    cv;
    wcel;
  };

  return 'wff' "x e. y";
}
