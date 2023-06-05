include "wceq.mm";
include "id.mm";
include "rexeqbidv.mm";

theorem rexeqbi1dv(wph: wff ph, wps: wff ps, vx: setvar x, cA: class A, cB: class B) {
  assume raleqbi1dv.1: |- "( A = B -> ( ph <-> ps ) )";

  disjoint A x;
  disjoint B x;



  do {
    cA;
    cB;
    wceq;
    #;
    wph;
    wps;
    vx;
    cA;
    cB;
    @0;
    id;
    raleqbi1dv.1;
    rexeqbidv;
  };

  return |- "( A = B -> ( E. x e. A ph <-> E. x e. B ps ) )";
}
