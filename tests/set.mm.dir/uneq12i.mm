include "wceq.mm";
include "cun.mm";
include "uneq12.mm";
include "mp2an.mm";

theorem uneq12i(cA: 'class' A, cB: 'class' B, cC: 'class' C, cD: 'class' D) {
  assume uneq1i.1: |- "A = B";
  assume uneq12i.2: |- "C = D";





  do {
    cA;
    cB;
    wceq;
    cC;
    cD;
    wceq;
    cA;
    cC;
    cun;
    cB;
    cD;
    cun;
    wceq;
    uneq1i.1;
    uneq12i.2;
    cA;
    cB;
    cC;
    cD;
    uneq12;
    mp2an;
  };

  return '|-' "( A u. C ) = ( B u. D )";
}
