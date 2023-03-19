include "cvv.mm"
include "wcel.mm"
include "ciun.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "dfiun3g.mm"
include "cv.mm"
include "a1i.mm"
include "mprg.mm"

theorem dfiun3
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume dfiun3.1: |- B e. _V


  assert |- U_ x e. A B = U. ran ( x e. A |-> B )

  proof
    cB
    cvv
    wcel
    #
    vx
    cA
    cB
    ciun
    vx
    cA
    cB
    cmpt
    crn
    cuni
    wceq
    vx
    cA
    vx
    cA
    cB
    cvv
    dfiun3g
    @0
    vx
    cv
    cA
    wcel
    dfiun3.1
    a1i
    mprg
end
