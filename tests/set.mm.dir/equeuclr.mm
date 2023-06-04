include "weq.mm";
include "wi.mm";
include "equtrr.mm";
include "equcoms.mm";

theorem equeuclr(vx: 'setvar' x, vy: 'setvar' y, vz: 'setvar' z) {





  do {
    vy;
    vz;
    weq;
    vy;
    vx;
    weq;
    wi;
    vz;
    vx;
    vz;
    vx;
    vy;
    equtrr;
    equcoms;
  };

  return '|-' "( x = z -> ( y = z -> y = x ) )";
}
