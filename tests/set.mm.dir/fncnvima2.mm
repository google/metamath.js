include "wfn.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "elpreima.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"

theorem fncnvima2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint F x
  disjoint B x
  assert |- ( F Fn A -> ( `' F " B ) = { x e. A | ( F ` x ) e. B } )

  proof
    cF
    cA
    wfn
    #
    cF
    ccnv
    cB
    cima
    #
    vx
    cv
    #
    cA
    wcel
    @2
    cF
    cfv
    cB
    wcel
    #
    wa
    #
    vx
    cab
    @3
    vx
    cA
    crab
    @0
    @4
    vx
    @1
    cA
    @2
    cB
    cF
    elpreima
    abbi2dv
    @3
    vx
    cA
    df-rab
    syl6eqr
end
