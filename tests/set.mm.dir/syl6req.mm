include "syl6eq.mm";
include "eqcomd.mm";

theorem syl6req(wph: 'wff' ph, cA: 'class' A, cB: 'class' B, cC: 'class' C) {
  assume syl6req.1: |- "( ph -> A = B )";
  assume syl6req.2: |- "B = C";





  do {
    wph;
    cA;
    cC;
    wph;
    cA;
    cB;
    cC;
    syl6req.1;
    syl6req.2;
    syl6eq;
    eqcomd;
  };

  return '|-' "( ph -> C = A )";
}
