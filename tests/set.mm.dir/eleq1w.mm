include "weq.mm";
include "cv.mm";
include "wcel.mm";
include "wa.mm";
include "wex.mm";
include "equequ2.mm";
include "anbi1d.mm";
include "exbidv.mm";
include "df-clel.mm";
include "3bitr4g.mm";

theorem eleq1w(vx: 'setvar' x, vy: 'setvar' y, cA: 'class' A) {



  let vz: setvar z;

  do {
    vx;
    vy;
    weq;
    #;
    vz;
    vx;
    weq;
    #;
    vz;
    cv;
    cA;
    wcel;
    #;
    wa;
    #;
    vz;
    wex;
    vz;
    vy;
    weq;
    #;
    @2;
    wa;
    #;
    vz;
    wex;
    vx;
    cv;
    #;
    cA;
    wcel;
    vy;
    cv;
    #;
    cA;
    wcel;
    @0;
    @3;
    @5;
    vz;
    @0;
    @1;
    @4;
    @2;
    vx;
    vy;
    vz;
    equequ2;
    anbi1d;
    exbidv;
    vz;
    @6;
    cA;
    df-clel;
    vz;
    @7;
    cA;
    df-clel;
    3bitr4g;
  };

  return '|-' "( x = y -> ( x e. A <-> y e. A ) )";
}
