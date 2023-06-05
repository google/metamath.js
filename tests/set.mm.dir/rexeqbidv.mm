include "cv.mm";
include "wcel.mm";
include "eleq2d.mm";
include "anbi12d.mm";
include "rexbidv2.mm";

theorem rexeqbidv(wph: wff ph, wps: wff ps, wch: wff ch, vx: setvar x, cA: class A, cB: class B) {
  assume raleqbidv.1: |- "( ph -> A = B )";
  assume raleqbidv.2: |- "( ph -> ( ps <-> ch ) )";

  disjoint ph x;



  do {
    wph;
    wps;
    wch;
    vx;
    cA;
    cB;
    wph;
    vx;
    cv;
    #;
    cA;
    wcel;
    @0;
    cB;
    wcel;
    wps;
    wch;
    wph;
    cA;
    cB;
    @0;
    raleqbidv.1;
    eleq2d;
    raleqbidv.2;
    anbi12d;
    rexbidv2;
  };

  return |- "( ph -> ( E. x e. A ps <-> E. x e. B ch ) )";
}
