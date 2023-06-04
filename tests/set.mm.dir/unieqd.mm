include "wceq.mm";
include "cuni.mm";
include "unieq.mm";
include "syl.mm";

theorem unieqd(wph: 'wff' ph, cA: 'class' A, cB: 'class' B) {
  assume unieqd.1: |- "( ph -> A = B )";





  do {
    wph;
    cA;
    cB;
    wceq;
    cA;
    cuni;
    cB;
    cuni;
    wceq;
    unieqd.1;
    cA;
    cB;
    unieq;
    syl;
  };

  return '|-' "( ph -> U. A = U. B )";
}
