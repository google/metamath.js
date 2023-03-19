include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "ssrexv.mm"
include "n0rex.mm"
include "impel.mm"

theorem ssn0rex
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A C_ B /\ A =/= (/) ) -> E. x e. B x e. A )

  proof
    cA
    cB
    wss
    vx
    cv
    cA
    wcel
    #
    vx
    cA
    wrex
    @0
    vx
    cB
    wrex
    cA
    c0
    wne
    @0
    vx
    cA
    cB
    ssrexv
    vx
    cA
    n0rex
    impel
end
