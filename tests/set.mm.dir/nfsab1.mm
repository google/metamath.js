include "cv.mm";
include "cab.mm";
include "wcel.mm";
include "hbab1.mm";
include "nf5i.mm";

theorem nfsab1(wph: wff ph, vx: setvar x, vy: setvar y) {

  disjoint x y;



  do {
    vy;
    cv;
    wph;
    vx;
    cab;
    wcel;
    vx;
    wph;
    vx;
    vy;
    hbab1;
    nf5i;
  };

  return |- "F/ x y e. { x | ph }";
}
