include "weq.mm";
include "wel.mm";
include "ax9.mm";
include "wi.mm";
include "equcoms.mm";
include "impbid.mm";

theorem elequ2(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {





  do {
    vx;
    vy;
    weq;
    vz;
    vx;
    wel;
    #;
    vz;
    vy;
    wel;
    #;
    vx;
    vy;
    vz;
    ax9;
    @1;
    @0;
    wi;
    vy;
    vx;
    vy;
    vx;
    vz;
    ax9;
    equcoms;
    impbid;
  };

  return $|-$ $( x = y -> ( z e. x <-> z e. y ) )$;
}
