include "eqtrd.mm";
include "eqcomd.mm";

theorem eqtr2d(wph: wff ph, cA: class A, cB: class B, cC: class C) {
  assume eqtr2d.1: |- "( ph -> A = B )";
  assume eqtr2d.2: |- "( ph -> B = C )";





  do {
    wph;
    cA;
    cC;
    wph;
    cA;
    cB;
    cC;
    eqtr2d.1;
    eqtr2d.2;
    eqtrd;
    eqcomd;
  };

  return |- "( ph -> C = A )";
}
