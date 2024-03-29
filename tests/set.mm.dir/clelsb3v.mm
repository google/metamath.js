include "cv.mm";
include "wcel.mm";
include "wsb.mm";
include "sbco2vv.mm";
include "nfv.mm";
include "eleq1w.mm";
include "sbiev.mm";
include "sbbii.mm";
include "3bitr3i.mm";

theorem clelsb3v(vx: setvar x, vy: setvar y, cA: class A) {

  disjoint A y;
  disjoint x y;
  disjoint A x;
  disjoint w y;
  disjoint A w;
  disjoint w x;

  let vw: setvar w;

  do {
    vw;
    cv;
    cA;
    wcel;
    #;
    vw;
    vy;
    wsb;
    #;
    vy;
    vx;
    wsb;
    @0;
    vw;
    vx;
    wsb;
    vy;
    cv;
    cA;
    wcel;
    #;
    vy;
    vx;
    wsb;
    vx;
    cv;
    cA;
    wcel;
    #;
    @0;
    vw;
    vx;
    vy;
    sbco2vv;
    @1;
    @2;
    vy;
    vx;
    @0;
    @2;
    vw;
    vy;
    @2;
    vw;
    nfv;
    vw;
    vy;
    cA;
    eleq1w;
    sbiev;
    sbbii;
    @0;
    @3;
    vw;
    vx;
    @3;
    vw;
    nfv;
    vw;
    vx;
    cA;
    eleq1w;
    sbiev;
    3bitr3i;
  };

  return |- "( [ x / y ] y e. A <-> x e. A )";
}
