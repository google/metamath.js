include "cv.mm"
include "ci.mm"
include "cdiv.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "cc.mm"
include "cim.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "df-im.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem imval
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( Im ` A ) = ( Re ` ( A / _i ) ) )

  proof
    vx
    cA
    vx
    cv
    #
    ci
    cdiv
    co
    #
    cre
    cfv
    cA
    ci
    cdiv
    co
    #
    cre
    cfv
    cc
    cim
    @0
    cA
    wceq
    @1
    @2
    cre
    @0
    cA
    ci
    cdiv
    oveq1
    fveq2d
    vx
    df-im
    @2
    cre
    fvex
    fvmpt
end
