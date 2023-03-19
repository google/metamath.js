include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "eqid.mm"
include "rnmpt.mm"
include "mptexg.mm"
include "rnexg.mm"
include "syl.mm"
include "syl5eqelr.mm"

theorem abrexexg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- ( A e. V -> { y | E. x e. A y = B } e. _V )

  proof
    cA
    cV
    wcel
    #
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cvv
    vx
    vy
    cA
    cB
    @1
    @1
    eqid
    rnmpt
    @0
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    vx
    cA
    cB
    cV
    mptexg
    @1
    cvv
    rnexg
    syl
    syl5eqelr
end
