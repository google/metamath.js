include "cab.mm";
include "wsb.mm";
include "cv.mm";
include "wcel.mm";
include "df-clab.mm";
include "3bitr4g.mm";
include "eqrdv.mm";

theorem abbilem(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x, vy: setvar y) {
  assume abbilem.1: |- "( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) )";

  disjoint x y;
  disjoint ph y;
  disjoint ps y;
  disjoint ch y;



  do {
    wph;
    vy;
    wps;
    vx;
    cab;
    #;
    wch;
    vx;
    cab;
    #;
    wph;
    wps;
    vx;
    vy;
    wsb;
    wch;
    vx;
    vy;
    wsb;
    vy;
    cv;
    #;
    @0;
    wcel;
    @2;
    @1;
    wcel;
    abbilem.1;
    wps;
    vy;
    vx;
    df-clab;
    wch;
    vy;
    vx;
    df-clab;
    3bitr4g;
    eqrdv;
  };

  return |- "( ph -> { x | ps } = { x | ch } )";
}
