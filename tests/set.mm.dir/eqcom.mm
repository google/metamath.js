include "wceq.mm";
include "id.mm";
include "eqcomd.mm";
include "impbii.mm";

theorem eqcom(cA: $class$ A, cB: $class$ B) {





  do {
    cA;
    cB;
    wceq;
    #;
    cB;
    cA;
    wceq;
    #;
    @0;
    cA;
    cB;
    @0;
    id;
    eqcomd;
    @1;
    cB;
    cA;
    @1;
    id;
    eqcomd;
    impbii;
  };

  return $|-$ $( A = B <-> B = A )$;
}
