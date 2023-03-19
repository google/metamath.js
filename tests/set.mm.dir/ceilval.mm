include "cv.mm"
include "cneg.mm"
include "cfl.mm"
include "cfv.mm"
include "cr.mm"
include "cceil.mm"
include "wceq.mm"
include "negeq.mm"
include "fveq2d.mm"
include "negeqd.mm"
include "df-ceil.mm"
include "negex.mm"
include "fvmpt.mm"

theorem ceilval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. RR -> ( |^ ` A ) = -u ( |_ ` -u A ) )

  proof
    vx
    cA
    vx
    cv
    #
    cneg
    #
    cfl
    cfv
    #
    cneg
    cA
    cneg
    #
    cfl
    cfv
    #
    cneg
    cr
    cceil
    @0
    cA
    wceq
    #
    @2
    @4
    @5
    @1
    @3
    cfl
    @0
    cA
    negeq
    fveq2d
    negeqd
    vx
    df-ceil
    @4
    negex
    fvmpt
end
