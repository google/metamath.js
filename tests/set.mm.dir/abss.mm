include "cab.mm";
include "wss.mm";
include "cv.mm";
include "wcel.mm";
include "wi.mm";
include "wal.mm";
include "abid2.mm";
include "sseq2i.mm";
include "ss2ab.mm";
include "bitr3i.mm";

theorem abss(wph: $wff$ ph, vx: $setvar$ x, cA: $class$ A) {

  disjoint A x;



  do {
    wph;
    vx;
    cab;
    #;
    cA;
    wss;
    @0;
    vx;
    cv;
    cA;
    wcel;
    #;
    vx;
    cab;
    #;
    wss;
    wph;
    @1;
    wi;
    vx;
    wal;
    @2;
    cA;
    @0;
    vx;
    cA;
    abid2;
    sseq2i;
    wph;
    @1;
    vx;
    ss2ab;
    bitr3i;
  };

  return $|-$ $( { x | ph } C_ A <-> A. x ( ph -> x e. A ) )$;
}
