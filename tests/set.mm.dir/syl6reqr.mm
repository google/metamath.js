include "eqcomi.mm";
include "syl6req.mm";

theorem syl6reqr(wph: $wff$ ph, cA: $class$ A, cB: $class$ B, cC: $class$ C) {
  assume syl6reqr.1: $|- ( ph -> A = B )$;
  assume syl6reqr.2: $|- C = B$;





  do {
    wph;
    cA;
    cB;
    cC;
    syl6reqr.1;
    cC;
    cB;
    syl6reqr.2;
    eqcomi;
    syl6req;
  };

  return $|-$ $( ph -> C = A )$;
}
