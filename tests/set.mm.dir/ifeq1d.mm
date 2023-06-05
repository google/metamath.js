include "wceq.mm";
include "cif.mm";
include "ifeq1.mm";
include "syl.mm";

theorem ifeq1d(wph: wff ph, wps: wff ps, cA: class A, cB: class B, cC: class C) {
  assume ifeq1d.1: |- "( ph -> A = B )";





  do {
    wph;
    cA;
    cB;
    wceq;
    wps;
    cA;
    cC;
    cif;
    wps;
    cB;
    cC;
    cif;
    wceq;
    ifeq1d.1;
    wps;
    cA;
    cB;
    cC;
    ifeq1;
    syl;
  };

  return |- "( ph -> if ( ps , A , C ) = if ( ps , B , C ) )";
}
