include "wceq.mm"
include "wral.mm"
include "cmpt.mm"
include "cv.mm"
include "wcel.mm"
include "eqidd.mm"
include "rgen.mm"
include "mpteq12.mm"
include "mpan2.mm"

theorem mpteq1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  assert |- ( A = B -> ( x e. A |-> C ) = ( x e. B |-> C ) )

  proof
    cA
    cB
    wceq
    cC
    cC
    wceq
    #
    vx
    cA
    wral
    vx
    cA
    cC
    cmpt
    vx
    cB
    cC
    cmpt
    wceq
    @0
    vx
    cA
    vx
    cv
    cA
    wcel
    cC
    eqidd
    rgen
    vx
    cA
    cC
    cB
    cC
    mpteq12
    mpan2
end
