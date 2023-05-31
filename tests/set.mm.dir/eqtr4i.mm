include "eqcomi.mm";
include "eqtri.mm";

theorem eqtr4i(cA: $class$ A, cB: $class$ B, cC: $class$ C) {
  assume eqtr4i.1: $|- A = B$;
  assume eqtr4i.2: $|- C = B$;





  do {
    cA;
    cB;
    cC;
    eqtr4i.1;
    cC;
    cB;
    eqtr4i.2;
    eqcomi;
    eqtri;
  };

  return $|-$ $A = C$;
}
