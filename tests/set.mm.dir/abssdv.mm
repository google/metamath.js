include "cv.mm";
include "wcel.mm";
include "wi.mm";
include "wal.mm";
include "cab.mm";
include "wss.mm";
include "alrimiv.mm";
include "abss.mm";
include "sylibr.mm";

theorem abssdv(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x, cA: 'class' A) {
  assume abssdv.1: |- "( ph -> ( ps -> x e. A ) )";

  disjoint ph x;
  disjoint A x;



  do {
    wph;
    wps;
    vx;
    cv;
    cA;
    wcel;
    wi;
    #;
    vx;
    wal;
    wps;
    vx;
    cab;
    cA;
    wss;
    wph;
    @0;
    vx;
    abssdv.1;
    alrimiv;
    wps;
    vx;
    cA;
    abss;
    sylibr;
  };

  return '|-' "( ph -> { x | ps } C_ A )";
}
