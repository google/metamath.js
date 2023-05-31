include "cab.mm";
include "cv.mm";
include "wcel.mm";
include "wsb.mm";
include "sbbidv.mm";
include "clelsb3v.mm";
include "bicomi.mm";
include "df-clab.mm";
include "3bitr4g.mm";
include "eqrdv.mm";

theorem abbi2dv(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x, cA: $class$ A) {
  assume abbi2dv.1: $|- ( ph -> ( x e. A <-> ps ) )$;

  disjoint A x;
  disjoint ph x;
  disjoint x y;
  disjoint A y;
  disjoint ph y;
  disjoint ps y;

  let vy: $setvar$ y;

  do {
    wph;
    vy;
    cA;
    wps;
    vx;
    cab;
    #;
    wph;
    vx;
    cv;
    cA;
    wcel;
    #;
    vx;
    vy;
    wsb;
    #;
    wps;
    vx;
    vy;
    wsb;
    vy;
    cv;
    #;
    cA;
    wcel;
    #;
    @3;
    @0;
    wcel;
    wph;
    @1;
    wps;
    vx;
    vy;
    abbi2dv.1;
    sbbidv;
    @2;
    @4;
    vy;
    vx;
    cA;
    clelsb3v;
    bicomi;
    wps;
    vy;
    vx;
    df-clab;
    3bitr4g;
    eqrdv;
  };

  return $|-$ $( ph -> A = { x | ps } )$;
}
