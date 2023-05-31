include "wceq.mm";
include "cun.mm";
include "uneq1.mm";
include "syl.mm";

theorem uneq1d(wph: $wff$ ph, cA: $class$ A, cB: $class$ B, cC: $class$ C) {
  assume uneq1d.1: $|- ( ph -> A = B )$;





  do {
    wph;
    cA;
    cB;
    wceq;
    cA;
    cC;
    cun;
    cB;
    cC;
    cun;
    wceq;
    uneq1d.1;
    cA;
    cB;
    cC;
    uneq1;
    syl;
  };

  return $|-$ $( ph -> ( A u. C ) = ( B u. C ) )$;
}
