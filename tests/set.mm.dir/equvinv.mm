include "weq.mm";
include "wa.mm";
include "wex.mm";
include "equequ1.mm";
include "equsexvw.mm";
include "bicomi.mm";

theorem equvinv(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {

  disjoint x z;
  disjoint y z;



  do {
    vz;
    vx;
    weq;
    vz;
    vy;
    weq;
    #;
    wa;
    vz;
    wex;
    vx;
    vy;
    weq;
    #;
    @0;
    @1;
    vz;
    vx;
    vz;
    vx;
    vy;
    equequ1;
    equsexvw;
    bicomi;
  };

  return $|-$ $( x = y <-> E. z ( z = x /\ z = y ) )$;
}
