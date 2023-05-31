include "cv.mm";
include "wcel.mm";
include "wb.mm";
include "wal.mm";
include "wceq.mm";
include "alrimiv.mm";
include "dfcleq.mm";
include "sylibr.mm";

theorem eqrdv(wph: $wff$ ph, vx: $setvar$ x, cA: $class$ A, cB: $class$ B) {
  assume eqrdv.1: $|- ( ph -> ( x e. A <-> x e. B ) )$;

  disjoint A x;
  disjoint B x;
  disjoint ph x;



  do {
    wph;
    vx;
    cv;
    #;
    cA;
    wcel;
    @0;
    cB;
    wcel;
    wb;
    #;
    vx;
    wal;
    cA;
    cB;
    wceq;
    wph;
    @1;
    vx;
    eqrdv.1;
    alrimiv;
    vx;
    cA;
    cB;
    dfcleq;
    sylibr;
  };

  return $|-$ $( ph -> A = B )$;
}
