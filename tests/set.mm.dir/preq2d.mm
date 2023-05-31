include "wceq.mm";
include "cpr.mm";
include "preq2.mm";
include "syl.mm";

theorem preq2d(wph: $wff$ ph, cA: $class$ A, cB: $class$ B, cC: $class$ C) {
  assume preq1d.1: $|- ( ph -> A = B )$;





  do {
    wph;
    cA;
    cB;
    wceq;
    cC;
    cA;
    cpr;
    cC;
    cB;
    cpr;
    wceq;
    preq1d.1;
    cA;
    cB;
    cC;
    preq2;
    syl;
  };

  return $|-$ $( ph -> { C , A } = { C , B } )$;
}
