include "wceq.mm";
include "id.mm";
include "eqeq2d.mm";

theorem eqeq2(cA: $class$ A, cB: $class$ B, cC: $class$ C) {





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
    eqeq2d;
  };

  return $|-$ $( A = B -> ( C = A <-> C = B ) )$;
}
