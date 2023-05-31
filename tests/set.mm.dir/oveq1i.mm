include "wceq.mm";
include "co.mm";
include "oveq1.mm";
include "ax-mp.mm";

theorem oveq1i(cA: $class$ A, cB: $class$ B, cC: $class$ C, cF: $class$ F) {
  assume oveq1i.1: $|- A = B$;





  do {
    cA;
    cB;
    wceq;
    cA;
    cC;
    cF;
    co;
    cB;
    cC;
    cF;
    co;
    wceq;
    oveq1i.1;
    cA;
    cB;
    cC;
    cF;
    oveq1;
    ax-mp;
  };

  return $|-$ $( A F C ) = ( B F C )$;
}
