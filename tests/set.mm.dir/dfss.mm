include "wss.mm";
include "cin.mm";
include "wceq.mm";
include "df-ss.mm";
include "eqcom.mm";
include "bitri.mm";

theorem dfss(cA: 'class' A, cB: 'class' B) {





  do {
    cA;
    cB;
    wss;
    cA;
    cB;
    cin;
    #;
    cA;
    wceq;
    cA;
    @0;
    wceq;
    cA;
    cB;
    df-ss;
    @0;
    cA;
    eqcom;
    bitri;
  };

  return '|-' "( A C_ B <-> A = ( A i^i B ) )";
}
