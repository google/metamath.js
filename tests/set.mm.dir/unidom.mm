include "wcel.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "ciun.mm"
include "cxp.mm"
include "uniiun.mm"
include "iundom.mm"
include "syl5eqbr.mm"

theorem unidom
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( ( A e. V /\ A. x e. A x ~<_ B ) -> U. A ~<_ ( A X. B ) )

  proof
    cA
    cV
    wcel
    vx
    cv
    #
    cB
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
    cA
    cB
    cxp
    cdom
    vx
    cA
    uniiun
    vx
    cA
    cB
    @0
    cV
    iundom
    syl5eqbr
end
