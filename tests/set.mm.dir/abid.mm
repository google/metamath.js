include "cv.mm";
include "cab.mm";
include "wcel.mm";
include "wsb.mm";
include "df-clab.mm";
include "sbid.mm";
include "bitri.mm";

theorem abid(wph: 'wff' ph, vx: 'setvar' x) {





  do {
    vx;
    cv;
    wph;
    vx;
    cab;
    wcel;
    wph;
    vx;
    vx;
    wsb;
    wph;
    wph;
    vx;
    vx;
    df-clab;
    wph;
    vx;
    sbid;
    bitri;
  };

  return '|-' "( x e. { x | ph } <-> ph )";
}
