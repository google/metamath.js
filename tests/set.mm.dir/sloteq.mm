include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cslot.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "df-slot.mm"
include "3eqtr4g.mm"

theorem sloteq
  let cA: class A
  let cB: class B
  let vf: setvar f


  assert |- ( A = B -> Slot A = Slot B )

  proof
    cA
    cB
    wceq
    #
    vf
    cvv
    cA
    vf
    cv
    #
    cfv
    #
    cmpt
    vf
    cvv
    cB
    @1
    cfv
    #
    cmpt
    cA
    cslot
    cB
    cslot
    @0
    vf
    cvv
    @2
    @3
    cA
    cB
    @1
    fveq2
    mpteq2dv
    vf
    cA
    df-slot
    vf
    cB
    df-slot
    3eqtr4g
end
