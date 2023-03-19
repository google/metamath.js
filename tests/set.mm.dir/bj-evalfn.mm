include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "cslot.mm"
include "fvex.mm"
include "df-slot.mm"
include "fnmpti.mm"

theorem bj-evalfn
  let cA: class A
  let vf: setvar f


  assert |- Slot A Fn _V

  proof
    vf
    cvv
    cA
    vf
    cv
    #
    cfv
    cA
    cslot
    cA
    @0
    fvex
    vf
    cA
    df-slot
    fnmpti
end
