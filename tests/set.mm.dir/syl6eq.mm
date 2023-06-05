include "wceq.mm";
include "a1i.mm";
include "eqtrd.mm";

theorem syl6eq(wph: wff ph, cA: class A, cB: class B, cC: class C) {
  assume syl6eq.1: |- "( ph -> A = B )";
  assume syl6eq.2: |- "B = C";





  do {
    wph;
    cA;
    cB;
    cC;
    syl6eq.1;
    cB;
    cC;
    wceq;
    wph;
    syl6eq.2;
    a1i;
    eqtrd;
  };

  return |- "( ph -> A = C )";
}
