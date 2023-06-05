include "wnfc.mm";
include "cv.mm";
include "wcel.mm";
include "wnf.mm";
include "df-nfc.mm";
include "mpgbir.mm";

theorem nfci(vx: setvar x, vy: setvar y, cA: class A) {
  assume nfci.1: |- "F/ x y e. A";

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
    vy;
    vx;
    vy;
    cA;
    df-nfc;
    nfci.1;
    mpgbir;
  };

  return |- "F/_ x A";
}
