include "cat.mm"
include "c0h.mm"
include "cv.mm"
include "ccv.mm"
include "wbr.mm"
include "cch.mm"
include "crab.mm"
include "df-at.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem atssch
  let cA: class A
  let vx: setvar x
  let cB: class B


  assert |- HAtoms C_ CH

  proof
    cat
    c0h
    vx
    cv
    ccv
    wbr
    #
    vx
    cch
    crab
    cch
    vx
    df-at
    @0
    vx
    cch
    ssrab2
    eqsstri
end
