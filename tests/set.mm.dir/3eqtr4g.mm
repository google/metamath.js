include "syl5eq.mm";
include "syl6eqr.mm";

theorem 3eqtr4g(wph: $wff$ ph, cA: $class$ A, cB: $class$ B, cC: $class$ C, cD: $class$ D) {
  assume 3eqtr4g.1: $|- ( ph -> A = B )$;
  assume 3eqtr4g.2: $|- C = A$;
  assume 3eqtr4g.3: $|- D = B$;





  do {
    wph;
    cC;
    cB;
    cD;
    wph;
    cC;
    cA;
    cB;
    3eqtr4g.2;
    3eqtr4g.1;
    syl5eq;
    3eqtr4g.3;
    syl6eqr;
  };

  return $|-$ $( ph -> C = D )$;
}
