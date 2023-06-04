include "weq.mm";
include "wi.mm";
include "ax7.mm";
include "equcoms.mm";

theorem equtr(vx: 'setvar' x, vy: 'setvar' y, vz: 'setvar' z) {





  do {
    vy;
    vz;
    weq;
    vx;
    vz;
    weq;
    wi;
    vy;
    vx;
    vy;
    vx;
    vz;
    ax7;
    equcoms;
  };

  return '|-' "( x = y -> ( y = z -> x = z ) )";
}
