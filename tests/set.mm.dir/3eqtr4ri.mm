include "eqtr4i.mm";

theorem 3eqtr4ri(cA: $class$ A, cB: $class$ B, cC: $class$ C, cD: $class$ D) {
  assume 3eqtr4i.1: $|- A = B$;
  assume 3eqtr4i.2: $|- C = A$;
  assume 3eqtr4i.3: $|- D = B$;





  do {
    cD;
    cA;
    cC;
    cD;
    cB;
    cA;
    3eqtr4i.3;
    3eqtr4i.1;
    eqtr4i;
    3eqtr4i.2;
    eqtr4i;
  };

  return $|-$ $D = C$;
}
