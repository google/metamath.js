include "wcel.mm";
include "eleq1i.mm";
include "mpbir.mm";

theorem eqeltri(cA: class A, cB: class B, cC: class C) {
  assume eqeltri.1: |- "A = B";
  assume eqeltri.2: |- "B e. C";





  do {
    cA;
    cC;
    wcel;
    cB;
    cC;
    wcel;
    eqeltri.2;
    cA;
    cB;
    cC;
    eqeltri.1;
    eleq1i;
    mpbir;
  };

  return |- "A e. C";
}
