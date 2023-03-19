include "cmpt.mm"
include "crn.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "eqid.mm"
include "rnmpt.mm"
include "mptex.mm"
include "rnex.mm"
include "eqeltrri.mm"

theorem abrexexOLD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume abrexex.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- { y | E. x e. A y = B } e. _V

  proof
    vx
    cA
    cB
    cmpt
    #
    crn
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    cvv
    vx
    vy
    cA
    cB
    @0
    @0
    eqid
    rnmpt
    @0
    vx
    cA
    cB
    abrexex.1
    mptex
    rnex
    eqeltrri
end
