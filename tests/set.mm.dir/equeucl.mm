include "weq.mm";
include "equeuclr.mm";
include "com12.mm";

theorem equeucl(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {





  do {
    vy;
    vz;
    weq;
    vx;
    vz;
    weq;
    vx;
    vy;
    weq;
    vy;
    vx;
    vz;
    equeuclr;
    com12;
  };

  return $|-$ $( x = z -> ( y = z -> x = y ) )$;
}
