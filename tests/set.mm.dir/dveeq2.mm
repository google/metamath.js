include "weq.mm";
include "wal.mm";
include "wn.mm";
include "nfeqf2.mm";
include "nf5rd.mm";

theorem dveeq2(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {

  disjoint x z;



  do {
    vx;
    vy;
    weq;
    vx;
    wal;
    wn;
    vz;
    vy;
    weq;
    vx;
    vx;
    vy;
    vz;
    nfeqf2;
    nf5rd;
  };

  return $|-$ $( -. A. x x = y -> ( z = y -> A. x z = y ) )$;
}
