include "wceq.mm";
include "id.mm";
include "eleq1d.mm";

theorem eleq1(cA: 'class' A, cB: 'class' B, cC: 'class' C) {





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
    eleq1d;
  };

  return '|-' "( A = B -> ( A e. C <-> B e. C ) )";
}
