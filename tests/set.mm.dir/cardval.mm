include "cvv.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfv.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "numth3.mm"
include "cardval3.mm"
include "mp2b.mm"

theorem cardval
  let vx: setvar x
  let cA: class A
  assume cardval.1: |- A e. _V

  disjoint A x
  assert |- ( card ` A ) = |^| { x e. On | x ~~ A }

  proof
    cA
    cvv
    wcel
    cA
    ccrd
    cdm
    wcel
    cA
    ccrd
    cfv
    vx
    cv
    cA
    cen
    wbr
    vx
    con0
    crab
    cint
    wceq
    cardval.1
    cA
    cvv
    numth3
    vx
    cA
    cardval3
    mp2b
end
