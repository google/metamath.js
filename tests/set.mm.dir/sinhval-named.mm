include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "cdiv.mm"
include "cc.mm"
include "csinh.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "df-sinh.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem sinhval-named
  let cA: class A
  let vx: setvar x
  let vk: setvar k


  assert |- ( A e. CC -> ( sinh ` A ) = ( ( sin ` ( _i x. A ) ) / _i ) )

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
    csin
    cfv
    #
    ci
    cdiv
    co
    ci
    cA
    cmul
    co
    #
    csin
    cfv
    #
    ci
    cdiv
    co
    cc
    csinh
    @0
    cA
    wceq
    #
    @2
    @4
    ci
    cdiv
    @5
    @1
    @3
    csin
    @0
    cA
    ci
    cmul
    oveq2
    fveq2d
    oveq1d
    vx
    df-sinh
    @4
    ci
    cdiv
    ovex
    fvmpt
end
