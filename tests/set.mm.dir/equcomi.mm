include "weq.mm";
include "equid.mm";
include "ax7.mm";
include "mpi.mm";

theorem equcomi(vx: setvar x, vy: setvar y) {





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
    ax7;
    mpi;
  };

  return |- "( x = y -> y = x )";
}
