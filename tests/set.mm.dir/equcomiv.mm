include "weq.mm";
include "equid.mm";
include "ax7v2.mm";
include "mpi.mm";

theorem equcomiv(vx: setvar x, vy: setvar y) {

  disjoint x y;



  do {
    vx;
    vy;
    weq;
    vx;
    vx;
    weq;
    vy;
    vx;
    weq;
    vx;
    equid;
    vx;
    vy;
    vx;
    ax7v2;
    mpi;
  };

  return |- "( x = y -> y = x )";
}
