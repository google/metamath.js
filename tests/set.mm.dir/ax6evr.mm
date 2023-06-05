include "weq.mm";
include "ax6ev.mm";
include "equcomiv.mm";
include "eximii.mm";

theorem ax6evr(vx: setvar x, vy: setvar y) {

  disjoint x y;



  do {
    vx;
    vy;
    weq;
    vy;
    vx;
    weq;
    vx;
    vx;
    vy;
    ax6ev;
    vx;
    vy;
    equcomiv;
    eximii;
  };

  return |- "E. x y = x";
}
