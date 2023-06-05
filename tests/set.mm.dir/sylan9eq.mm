include "wceq.mm";
include "eqtr.mm";
include "syl2an.mm";

theorem sylan9eq(wph: wff ph, wps: wff ps, cA: class A, cB: class B, cC: class C) {
  assume sylan9eq.1: |- "( ph -> A = B )";
  assume sylan9eq.2: |- "( ps -> B = C )";





  do {
    wph;
    cA;
    cB;
    wceq;
    cB;
    cC;
    wceq;
    cA;
    cC;
    wceq;
    wps;
    sylan9eq.1;
    sylan9eq.2;
    cA;
    cB;
    cC;
    eqtr;
    syl2an;
  };

  return |- "( ( ph /\\ ps ) -> A = C )";
}
