include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "cslot.mm"
include "df-slot.mm"
include "funmpt2.mm"

theorem bj-evalfun
  let cA: class A
  let vf: setvar f


  assert |- Fun Slot A

  proof
    vf
    cvv
    cA
    vf
    cv
    cfv
    cA
    cslot
    vf
    cA
    df-slot
    funmpt2
end
