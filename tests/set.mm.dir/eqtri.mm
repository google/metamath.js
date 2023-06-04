include "wceq.mm";
include "eqeq2i.mm";
include "mpbi.mm";

theorem eqtri(cA: 'class' A, cB: 'class' B, cC: 'class' C) {
  assume eqtri.1: |- "A = B";
  assume eqtri.2: |- "B = C";





  do {
    cA;
    cB;
    wceq;
    cA;
    cC;
    wceq;
    eqtri.1;
    cB;
    cC;
    cA;
    eqtri.2;
    eqeq2i;
    mpbi;
  };

  return '|-' "A = C";
}
