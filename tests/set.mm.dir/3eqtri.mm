include "eqtri.mm";

theorem 3eqtri(cA: $class$ A, cB: $class$ B, cC: $class$ C, cD: $class$ D) {
  assume 3eqtri.1: $|- A = B$;
  assume 3eqtri.2: $|- B = C$;
  assume 3eqtri.3: $|- C = D$;





  do {
    cA;
    cB;
    cD;
    3eqtri.1;
    cB;
    cC;
    cD;
    3eqtri.2;
    3eqtri.3;
    eqtri;
    eqtri;
  };

  return $|-$ $A = D$;
}
