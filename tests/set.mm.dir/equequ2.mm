include "weq.mm";
include "equtrr.mm";
include "equeuclr.mm";
include "impbid.mm";

theorem equequ2(vx: 'setvar' x, vy: 'setvar' y, vz: 'setvar' z) {





  do {
    vx;
    vy;
    weq;
    vz;
    vx;
    weq;
    vz;
    vy;
    weq;
    vx;
    vy;
    vz;
    equtrr;
    vx;
    vz;
    vy;
    equeuclr;
    impbid;
  };

  return '|-' "( x = y -> ( z = x <-> z = y ) )";
}
