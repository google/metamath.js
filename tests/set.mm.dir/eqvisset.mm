include "cv.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "eleq1.mm"
include "mpbii.mm"

theorem eqvisset
  let vx: setvar x
  let cA: class A


  assert |- ( x = A -> A e. _V )

  proof
    vx
    cv
    #
    cA
    wceq
    @0
    cvv
    wcel
    cA
    cvv
    wcel
    vx
    vex
    @0
    cA
    cvv
    eleq1
    mpbii
end
