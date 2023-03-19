include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "crab.mm"
include "cuni.mm"
include "csn.mm"
include "rabsn.mm"
include "unieqd.mm"
include "unisng.mm"
include "eqtrd.mm"

theorem unisn3
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A e. B -> U. { x e. B | x = A } = A )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    cA
    wceq
    vx
    cB
    crab
    #
    cuni
    cA
    csn
    #
    cuni
    cA
    @0
    @1
    @2
    vx
    cB
    cA
    rabsn
    unieqd
    cA
    cB
    unisng
    eqtrd
end
