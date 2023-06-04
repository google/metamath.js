include "cab.mm";
include "wceq.mm";
include "wtru.mm";
include "wb.mm";
include "a1i.mm";
include "abbidv.mm";
include "mptru.mm";

theorem abbii(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume abbii.1: |- "( ph <-> ps )";



  let vy: setvar y;

  do {
    wph;
    vx;
    cab;
    wps;
    vx;
    cab;
    wceq;
    wtru;
    wph;
    wps;
    vx;
    wph;
    wps;
    wb;
    wtru;
    abbii.1;
    a1i;
    abbidv;
    mptru;
  };

  return '|-' "{ x | ph } = { x | ps }";
}
