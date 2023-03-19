include "wcel.mm"
include "cvv.mm"
include "cslot.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "fveq1.mm"
include "df-slot.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem bj-evalval
  let cA: class A
  let cF: class F
  let cV: class V
  let vf: setvar f


  assert |- ( F e. V -> ( Slot A ` F ) = ( F ` A ) )

  proof
    cF
    cV
    wcel
    cF
    cvv
    wcel
    cF
    cA
    cslot
    #
    cfv
    cA
    cF
    cfv
    #
    wceq
    cF
    cV
    elex
    vf
    cF
    cA
    vf
    cv
    #
    cfv
    @1
    cvv
    @0
    cA
    @2
    cF
    fveq1
    vf
    cA
    df-slot
    cA
    cF
    fvex
    fvmpt
    syl
end
