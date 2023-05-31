include "wceq.mm";
include "biidd.mm";
include "rexeqbi1dv.mm";

theorem rexeq(wph: $wff$ ph, vx: $setvar$ x, cA: $class$ A, cB: $class$ B) {

  disjoint A x;
  disjoint B x;



  do {
    wph;
    wph;
    vx;
    cA;
    cB;
    cA;
    cB;
    wceq;
    wph;
    biidd;
    rexeqbi1dv;
  };

  return $|-$ $( A = B -> ( E. x e. A ph <-> E. x e. B ph ) )$;
}
