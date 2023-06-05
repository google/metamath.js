include "wceq.mm";
include "id.mm";
include "eleq2d.mm";

theorem eleq2(cA: class A, cB: class B, cC: class C) {





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
    eleq2d;
  };

  return |- "( A = B -> ( C e. A <-> C e. B ) )";
}
