include "cv.mm";
include "wcel.mm";
include "wb.mm";
include "wtru.mm";
include "cab.mm";
include "wceq.mm";
include "a1i.mm";
include "abeq2d.mm";
include "mptru.mm";

theorem abeq2i(wph: wff ph, vx: setvar x, cA: class A) {
  assume abeq2i.1: |- "A = { x | ph }";





  do {
    vx;
    cv;
    cA;
    wcel;
    wph;
    wb;
    wtru;
    wph;
    vx;
    cA;
    cA;
    wph;
    vx;
    cab;
    wceq;
    wtru;
    abeq2i.1;
    a1i;
    abeq2d;
    mptru;
  };

  return |- "( x e. A <-> ph )";
}
