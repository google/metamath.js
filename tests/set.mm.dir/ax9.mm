include "weq.mm";
include "wa.mm";
include "wex.mm";
include "wel.mm";
include "wi.mm";
include "equvinv.mm";
include "ax9v2.mm";
include "equcoms.mm";
include "ax9v1.mm";
include "sylan9.mm";
include "exlimiv.mm";
include "sylbi.mm";

theorem ax9(vx: setvar x, vy: setvar y, vz: setvar z) {



  let vt: setvar t;

  do {
    vx;
    vy;
    weq;
    vt;
    vx;
    weq;
    #;
    vt;
    vy;
    weq;
    #;
    wa;
    #;
    vt;
    wex;
    vz;
    vx;
    wel;
    #;
    vz;
    vy;
    wel;
    #;
    wi;
    #;
    vx;
    vy;
    vt;
    equvinv;
    @2;
    @5;
    vt;
    @0;
    @3;
    vz;
    vt;
    wel;
    #;
    @1;
    @4;
    @3;
    @6;
    wi;
    vx;
    vt;
    vx;
    vt;
    vz;
    ax9v2;
    equcoms;
    vt;
    vy;
    vz;
    ax9v1;
    sylan9;
    exlimiv;
    sylbi;
  };

  return |- "( x = y -> ( z e. x -> z e. y ) )";
}
