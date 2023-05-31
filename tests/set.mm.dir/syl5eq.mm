include "wceq.mm";
include "a1i.mm";
include "eqtrd.mm";

theorem syl5eq(wph: $wff$ ph, cA: $class$ A, cB: $class$ B, cC: $class$ C) {
  assume syl5eq.1: $|- A = B$;
  assume syl5eq.2: $|- ( ph -> B = C )$;





  do {
    wph;
    cA;
    cB;
    cC;
    cA;
    cB;
    wceq;
    wph;
    syl5eq.1;
    a1i;
    syl5eq.2;
    eqtrd;
  };

  return $|-$ $( ph -> A = C )$;
}
