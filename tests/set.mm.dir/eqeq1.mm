include "wceq.mm";
include "id.mm";
include "eqeq1d.mm";

theorem eqeq1(cA: $class$ A, cB: $class$ B, cC: $class$ C) {





  do {
    cA;
    cB;
    wceq;
    #;
    cA;
    cB;
    cC;
    @0;
    id;
    eqeq1d;
  };

  return $|-$ $( A = B -> ( A = C <-> B = C ) )$;
}
