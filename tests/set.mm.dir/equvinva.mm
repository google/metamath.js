include "weq.mm";
include "wex.mm";
include "wa.mm";
include "ax6evr.mm";
include "equtr.mm";
include "ancrd.mm";
include "eximdv.mm";
include "mpi.mm";

theorem equvinva(vx: setvar x, vy: setvar y, vz: setvar z) {

  disjoint x z;
  disjoint y z;



  do {
    vx;
    vy;
    weq;
    #;
    vy;
    vz;
    weq;
    #;
    vz;
    wex;
    vx;
    vz;
    weq;
    #;
    @1;
    wa;
    #;
    vz;
    wex;
    vz;
    vy;
    ax6evr;
    @0;
    @1;
    @3;
    vz;
    @0;
    @1;
    @2;
    vx;
    vy;
    vz;
    equtr;
    ancrd;
    eximdv;
    mpi;
  };

  return |- "( x = y -> E. z ( x = z /\\ y = z ) )";
}
