include "eqcomi.mm";
include "syl6eq.mm";

theorem syl6eqr(wph: 'wff' ph, cA: 'class' A, cB: 'class' B, cC: 'class' C) {
  assume syl6eqr.1: |- "( ph -> A = B )";
  assume syl6eqr.2: |- "C = B";





  do {
    wph;
    cA;
    cB;
    cC;
    syl6eqr.1;
    cC;
    cB;
    syl6eqr.2;
    eqcomi;
    syl6eq;
  };

  return '|-' "( ph -> A = C )";
}
