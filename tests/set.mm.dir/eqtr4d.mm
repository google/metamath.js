include "eqcomd.mm";
include "eqtrd.mm";

theorem eqtr4d(wph: $wff$ ph, cA: $class$ A, cB: $class$ B, cC: $class$ C) {
  assume eqtr4d.1: $|- ( ph -> A = B )$;
  assume eqtr4d.2: $|- ( ph -> C = B )$;





  do {
    wph;
    cA;
    cB;
    cC;
    eqtr4d.1;
    wph;
    cC;
    cB;
    eqtr4d.2;
    eqcomd;
    eqtrd;
  };

  return $|-$ $( ph -> A = C )$;
}
