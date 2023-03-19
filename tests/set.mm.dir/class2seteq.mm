include "wcel.mm"
include "cvv.mm"
include "crab.mm"
include "wceq.mm"
include "elex.mm"
include "wral.mm"
include "cv.mm"
include "ax-1.mm"
include "ralrimiv.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqcomd.mm"
include "syl.mm"

theorem class2seteq
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( A e. V -> { x e. A | A e. _V } = A )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    @0
    vx
    cA
    crab
    #
    cA
    wceq
    cA
    cV
    elex
    @0
    cA
    @1
    @0
    @0
    vx
    cA
    wral
    cA
    @1
    wceq
    @0
    @0
    vx
    cA
    @0
    vx
    cv
    cA
    wcel
    ax-1
    ralrimiv
    @0
    vx
    cA
    rabid2
    sylibr
    eqcomd
    syl
end
