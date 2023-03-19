include "wfn.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "wceq.mm"
include "fncnvima2.mm"
include "fvex.mm"
include "elsn.mm"
include "rabbii.mm"
include "syl6eq.mm"

theorem fniniseg2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint F x
  disjoint B x
  assert |- ( F Fn A -> ( `' F " { B } ) = { x e. A | ( F ` x ) = B } )

  proof
    cF
    cA
    wfn
    cF
    ccnv
    cB
    csn
    #
    cima
    vx
    cv
    #
    cF
    cfv
    #
    @0
    wcel
    #
    vx
    cA
    crab
    @2
    cB
    wceq
    #
    vx
    cA
    crab
    vx
    cA
    @0
    cF
    fncnvima2
    @3
    @4
    vx
    cA
    @2
    cB
    @1
    cF
    fvex
    elsn
    rabbii
    syl6eq
end
