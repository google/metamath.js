include "wceq.mm";
include "co.mm";
include "oveq2.mm";
include "ax-mp.mm";

theorem oveq2i(cA: class A, cB: class B, cC: class C, cF: class F) {
  assume oveq1i.1: |- "A = B";





  do {
    cA;
    cB;
    wceq;
    cC;
    cA;
    cF;
    co;
    cC;
    cB;
    cF;
    co;
    wceq;
    oveq1i.1;
    cA;
    cB;
    cC;
    cF;
    oveq2;
    ax-mp;
  };

  return |- "( C F A ) = ( C F B )";
}
