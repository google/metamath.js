include "wceq.mm";
include "cfv.mm";
include "fveq2.mm";
include "syl.mm";

theorem fveq2d(wph: 'wff' ph, cA: 'class' A, cB: 'class' B, cF: 'class' F) {
  assume fveq2d.1: |- "( ph -> A = B )";





  do {
    wph;
    cA;
    cB;
    wceq;
    cA;
    cF;
    cfv;
    cB;
    cF;
    cfv;
    wceq;
    fveq2d.1;
    cA;
    cB;
    cF;
    fveq2;
    syl;
  };

  return '|-' "( ph -> ( F ` A ) = ( F ` B ) )";
}
