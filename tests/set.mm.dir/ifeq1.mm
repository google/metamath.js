include "wceq.mm";
include "crab.mm";
include "wn.mm";
include "cun.mm";
include "cif.mm";
include "rabeq.mm";
include "uneq1d.mm";
include "dfif6.mm";
include "3eqtr4g.mm";

theorem ifeq1(wph: wff ph, cA: class A, cB: class B, cC: class C) {



  let vx: setvar x;

  do {
    cA;
    cB;
    wceq;
    #;
    wph;
    vx;
    cA;
    crab;
    #;
    wph;
    wn;
    vx;
    cC;
    crab;
    #;
    cun;
    wph;
    vx;
    cB;
    crab;
    #;
    @2;
    cun;
    wph;
    cA;
    cC;
    cif;
    wph;
    cB;
    cC;
    cif;
    @0;
    @1;
    @3;
    @2;
    wph;
    vx;
    cA;
    cB;
    rabeq;
    uneq1d;
    wph;
    vx;
    cA;
    cC;
    dfif6;
    wph;
    vx;
    cB;
    cC;
    dfif6;
    3eqtr4g;
  };

  return |- "( A = B -> if ( ph , A , C ) = if ( ph , B , C ) )";
}
