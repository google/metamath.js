include "wceq.mm";
include "eqid.mm";
include "eqeq1d.mm";
include "mpbii.mm";

theorem eqcomd(wph: wff ph, cA: class A, cB: class B) {
  assume eqcomd.1: |- "( ph -> A = B )";





  do {
    wph;
    cA;
    cA;
    wceq;
    cB;
    cA;
    wceq;
    cA;
    eqid;
    wph;
    cA;
    cB;
    cA;
    eqcomd.1;
    eqeq1d;
    mpbii;
  };

  return |- "( ph -> B = A )";
}
