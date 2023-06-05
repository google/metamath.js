include "wceq.mm";
include "eqeq1d.mm";
include "eqcom.mm";
include "3bitr4g.mm";

theorem eqeq2d(wph: wff ph, cA: class A, cB: class B, cC: class C) {
  assume eqeq2d.1: |- "( ph -> A = B )";





  do {
    wph;
    cA;
    cC;
    wceq;
    cB;
    cC;
    wceq;
    cC;
    cA;
    wceq;
    cC;
    cB;
    wceq;
    wph;
    cA;
    cB;
    cC;
    eqeq2d.1;
    eqeq1d;
    cC;
    cA;
    eqcom;
    cC;
    cB;
    eqcom;
    3bitr4g;
  };

  return |- "( ph -> ( C = A <-> C = B ) )";
}
