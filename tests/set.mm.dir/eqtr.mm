include "wceq.mm";
include "eqeq1.mm";
include "biimpar.mm";

theorem eqtr(cA: class A, cB: class B, cC: class C) {





  do {
    cA;
    cB;
    wceq;
    cA;
    cC;
    wceq;
    cB;
    cC;
    wceq;
    cA;
    cB;
    cC;
    eqeq1;
    biimpar;
  };

  return |- "( ( A = B /\\ B = C ) -> A = C )";
}
