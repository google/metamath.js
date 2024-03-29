include "wceq.mm";
include "eqcom.mm";
include "mpbi.mm";

theorem eqcomi(cA: class A, cB: class B) {
  assume eqcomi.1: |- "A = B";





  do {
    cA;
    cB;
    wceq;
    cB;
    cA;
    wceq;
    eqcomi.1;
    cA;
    cB;
    eqcom;
    mpbi;
  };

  return |- "B = A";
}
