include "wceq.mm";
include "wcel.mm";
include "wb.mm";
include "eleq2.mm";
include "ax-mp.mm";

theorem eleq2i(cA: class A, cB: class B, cC: class C) {
  assume eleq1i.1: |- "A = B";





  do {
    cA;
    cB;
    wceq;
    cC;
    cA;
    wcel;
    cC;
    cB;
    wcel;
    wb;
    eleq1i.1;
    cA;
    cB;
    cC;
    eleq2;
    ax-mp;
  };

  return |- "( C e. A <-> C e. B )";
}
