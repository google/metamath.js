include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "cvv.mm"
include "numth3.mm"
include "ax-mp.mm"
include "isnum2.mm"
include "mpbi.mm"

theorem numth2
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  assume numth.1: |- A e. _V

  disjoint A x
  disjoint f x
  disjoint A f
  assert |- E. x e. On x ~~ A

  proof
    cA
    ccrd
    cdm
    wcel
    #
    vx
    cv
    cA
    cen
    wbr
    vx
    con0
    wrex
    cA
    cvv
    wcel
    @0
    numth.1
    cA
    cvv
    numth3
    ax-mp
    vx
    cA
    isnum2
    mpbi
end
