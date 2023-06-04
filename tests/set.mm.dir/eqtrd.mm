include "wceq.mm";
include "eqeq2d.mm";
include "mpbid.mm";

theorem eqtrd(wph: 'wff' ph, cA: 'class' A, cB: 'class' B, cC: 'class' C) {
  assume eqtrd.1: |- "( ph -> A = B )";
  assume eqtrd.2: |- "( ph -> B = C )";





  do {
    wph;
    cA;
    cB;
    wceq;
    cA;
    cC;
    wceq;
    eqtrd.1;
    wph;
    cB;
    cC;
    cA;
    eqtrd.2;
    eqeq2d;
    mpbid;
  };

  return '|-' "( ph -> A = C )";
}
