include "weq.mm";
include "ax7.mm";
include "equtr.mm";
include "impbid.mm";

theorem equequ1(vx: setvar x, vy: setvar y, vz: setvar z) {





  do {
    vx;
    vy;
    weq;
    vx;
    vz;
    weq;
    vy;
    vz;
    weq;
    vx;
    vy;
    vz;
    ax7;
    vx;
    vy;
    vz;
    equtr;
    impbid;
  };

  return |- "( x = y -> ( x = z <-> y = z ) )";
}
