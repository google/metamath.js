include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "cc.mm"
include "ccosh.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "df-cosh.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem coshval-named
  let cA: class A
  let vx: setvar x
  let vk: setvar k


  assert |- ( A e. CC -> ( cosh ` A ) = ( cos ` ( _i x. A ) ) )

  proof
    vx
    cA
    ci
    vx
    cv
    #
    cmul
    co
    #
    ccos
    cfv
    ci
    cA
    cmul
    co
    #
    ccos
    cfv
    cc
    ccosh
    @0
    cA
    wceq
    @1
    @2
    ccos
    @0
    cA
    ci
    cmul
    oveq2
    fveq2d
    vx
    df-cosh
    @2
    ccos
    fvex
    fvmpt
end
