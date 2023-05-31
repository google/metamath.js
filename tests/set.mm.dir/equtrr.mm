include "weq.mm";
include "equtr.mm";
include "com12.mm";

theorem equtrr(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {





  do {
    vz;
    vx;
    weq;
    vx;
    vy;
    weq;
    vz;
    vy;
    weq;
    vz;
    vx;
    vy;
    equtr;
    com12;
  };

  return $|-$ $( x = y -> ( z = x -> z = y ) )$;
}
