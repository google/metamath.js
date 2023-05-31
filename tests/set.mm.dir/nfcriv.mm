include "wnfc.mm";
include "cv.mm";
include "wcel.mm";
include "wnf.mm";
include "nfcr.mm";
include "ax-mp.mm";

theorem nfcriv(vx: $setvar$ x, vy: $setvar$ y, cA: $class$ A) {
  assume nfcriv.1: $|- F/_ x A$;

  disjoint x y;
  disjoint A y;



  do {
    vx;
    cA;
    wnfc;
    vy;
    cv;
    cA;
    wcel;
    vx;
    wnf;
    nfcriv.1;
    vx;
    vy;
    cA;
    nfcr;
    ax-mp;
  };

  return $|-$ $F/ x y e. A$;
}
