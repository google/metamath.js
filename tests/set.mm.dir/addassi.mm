include "cc.mm";
include "wcel.mm";
include "caddc.mm";
include "co.mm";
include "wceq.mm";
include "addass.mm";
include "mp3an.mm";

theorem addassi(cA: class A, cB: class B, cC: class C) {
  assume axi.1: |- "A e. CC";
  assume axi.2: |- "B e. CC";
  assume axi.3: |- "C e. CC";





  do {
    cA;
    cc;
    wcel;
    cB;
    cc;
    wcel;
    cC;
    cc;
    wcel;
    cA;
    cB;
    caddc;
    co;
    cC;
    caddc;
    co;
    cA;
    cB;
    cC;
    caddc;
    co;
    caddc;
    co;
    wceq;
    axi.1;
    axi.2;
    axi.3;
    cA;
    cB;
    cC;
    addass;
    mp3an;
  };

  return |- "( ( A + B ) + C ) = ( A + ( B + C ) )";
}
