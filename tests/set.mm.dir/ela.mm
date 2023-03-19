include "c0h.mm"
include "cv.mm"
include "ccv.mm"
include "wbr.mm"
include "cch.mm"
include "cat.mm"
include "breq2.mm"
include "df-at.mm"
include "elrab2.mm"

theorem ela
  let cA: class A
  let vx: setvar x
  let cB: class B


  assert |- ( A e. HAtoms <-> ( A e. CH /\ 0H <oH A ) )

  proof
    c0h
    vx
    cv
    #
    ccv
    wbr
    c0h
    cA
    ccv
    wbr
    vx
    cA
    cch
    cat
    @0
    cA
    c0h
    ccv
    breq2
    vx
    df-at
    elrab2
end
