include "cab.mm";
include "wceq.mm";
include "wtru.mm";
include "cv.mm";
include "wcel.mm";
include "wb.mm";
include "a1i.mm";
include "abbi2dv.mm";
include "mptru.mm";

theorem abbi2i(wph: $wff$ ph, vx: $setvar$ x, cA: $class$ A) {
  assume abbi2i.1: $|- ( x e. A <-> ph )$;

  disjoint A x;
  disjoint x y;
  disjoint A y;
  disjoint ph y;

  let vy: $setvar$ y;

  do {
    cA;
    wph;
    vx;
    cab;
    wceq;
    wtru;
    wph;
    vx;
    cA;
    vx;
    cv;
    cA;
    wcel;
    wph;
    wb;
    wtru;
    abbi2i.1;
    a1i;
    abbi2dv;
    mptru;
  };

  return $|-$ $A = { x | ph }$;
}
