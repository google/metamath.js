include "cv.mm"
include "wceq.mm"
include "w3o.mm"
include "ctp.mm"
include "vex.mm"
include "eltp.mm"
include "abbi2i.mm"

theorem dftp2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- { A , B , C } = { x | ( x = A \/ x = B \/ x = C ) }

  proof
    vx
    cv
    #
    cA
    wceq
    @0
    cB
    wceq
    @0
    cC
    wceq
    w3o
    vx
    cA
    cB
    cC
    ctp
    @0
    cA
    cB
    cC
    vx
    vex
    eltp
    abbi2i
end
