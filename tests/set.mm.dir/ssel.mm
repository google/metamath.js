include "wss.mm";
include "cv.mm";
include "wceq.mm";
include "wcel.mm";
include "wa.mm";
include "wex.mm";
include "wi.mm";
include "wal.mm";
include "dfss2.mm";
include "biimpi.mm";
include "19.21bi.mm";
include "anim2d.mm";
include "eximdv.mm";
include "df-clel.mm";
include "3imtr4g.mm";

theorem ssel(cA: 'class' A, cB: 'class' B, cC: 'class' C) {



  let vx: setvar x;

  do {
    cA;
    cB;
    wss;
    #;
    vx;
    cv;
    #;
    cC;
    wceq;
    #;
    @1;
    cA;
    wcel;
    #;
    wa;
    #;
    vx;
    wex;
    @2;
    @1;
    cB;
    wcel;
    #;
    wa;
    #;
    vx;
    wex;
    cC;
    cA;
    wcel;
    cC;
    cB;
    wcel;
    @0;
    @4;
    @6;
    vx;
    @0;
    @3;
    @5;
    @2;
    @0;
    @3;
    @5;
    wi;
    #;
    vx;
    @0;
    @7;
    vx;
    wal;
    vx;
    cA;
    cB;
    dfss2;
    biimpi;
    19.21bi;
    anim2d;
    eximdv;
    vx;
    cC;
    cA;
    df-clel;
    vx;
    cC;
    cB;
    df-clel;
    3imtr4g;
  };

  return '|-' "( A C_ B -> ( C e. A -> C e. B ) )";
}
