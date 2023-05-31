include "wceq.mm";
include "wb.mm";
include "eqeq2.mm";
include "ax-mp.mm";

theorem eqeq2i(cA: $class$ A, cB: $class$ B, cC: $class$ C) {
  assume eqeq2i.1: $|- A = B$;





  do {
    cA;
    cB;
    wceq;
    cC;
    cA;
    wceq;
    cC;
    cB;
    wceq;
    wb;
    eqeq2i.1;
    cA;
    cB;
    cC;
    eqeq2;
    ax-mp;
  };

  return $|-$ $( C = A <-> C = B )$;
}
