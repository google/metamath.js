include "cv.mm";
include "wcel.mm";
include "wa.mm";
include "wex.mm";
include "wrex.mm";
include "exbidv.mm";
include "df-rex.mm";
include "3bitr4g.mm";

theorem rexbidv2(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, vx: 'setvar' x, cA: 'class' A, cB: 'class' B) {
  assume rexbidv2.1: |- "( ph -> ( ( x e. A /\\ ps ) <-> ( x e. B /\\ ch ) ) )";

  disjoint ph x;



  do {
    wph;
    vx;
    cv;
    #;
    cA;
    wcel;
    wps;
    wa;
    #;
    vx;
    wex;
    @0;
    cB;
    wcel;
    wch;
    wa;
    #;
    vx;
    wex;
    wps;
    vx;
    cA;
    wrex;
    wch;
    vx;
    cB;
    wrex;
    wph;
    @1;
    @2;
    vx;
    rexbidv2.1;
    exbidv;
    wps;
    vx;
    cA;
    df-rex;
    wch;
    vx;
    cB;
    df-rex;
    3bitr4g;
  };

  return '|-' "( ph -> ( E. x e. A ps <-> E. x e. B ch ) )";
}
