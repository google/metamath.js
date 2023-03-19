include "cvv.mm"
include "wcel.mm"
include "ciin.mm"
include "cmpt.mm"
include "crn.mm"
include "cint.mm"
include "wceq.mm"
include "dfiin3g.mm"
include "cv.mm"
include "a1i.mm"
include "mprg.mm"

theorem dfiin3
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume dfiun3.1: |- B e. _V


  assert |- |^|_ x e. A B = |^| ran ( x e. A |-> B )

  proof
    cB
    cvv
    wcel
    #
    vx
    cA
    cB
    ciin
    vx
    cA
    cB
    cmpt
    crn
    cint
    wceq
    vx
    cA
    vx
    cA
    cB
    cvv
    dfiin3g
    @0
    vx
    cv
    cA
    wcel
    dfiun3.1
    a1i
    mprg
end
