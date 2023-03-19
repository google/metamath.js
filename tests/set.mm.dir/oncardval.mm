include "con0.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfv.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "onenon.mm"
include "cardval3.mm"
include "syl.mm"

theorem oncardval
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. On -> ( card ` A ) = |^| { x e. On | x ~~ A } )

  proof
    cA
    con0
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
    cA
    onenon
    vx
    cA
    cardval3
    syl
end
