include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "ciun.mm"
include "uniiun.mm"
include "iunctb.mm"
include "syl5eqbr.mm"

theorem unictb
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A ~<_ _om /\ A. x e. A x ~<_ _om ) -> U. A ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    vx
    cv
    #
    com
    cdom
    wbr
    vx
    cA
    wral
    wa
    cA
    cuni
    vx
    cA
    @0
    ciun
    com
    cdom
    vx
    cA
    uniiun
    vx
    cA
    @0
    iunctb
    syl5eqbr
end
