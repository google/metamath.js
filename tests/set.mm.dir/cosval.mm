include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cc.mm"
include "ccos.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "df-cos.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem cosval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. CC -> ( cos ` A ) = ( ( ( exp ` ( _i x. A ) ) + ( exp ` ( -u _i x. A ) ) ) / 2 ) )

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
    ce
    cfv
    #
    ci
    cneg
    #
    @0
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    @3
    cA
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    cc
    ccos
    @0
    cA
    wceq
    #
    @6
    @11
    c2
    cdiv
    @12
    @2
    @8
    @5
    @10
    caddc
    @12
    @1
    @7
    ce
    @0
    cA
    ci
    cmul
    oveq2
    fveq2d
    @12
    @4
    @9
    ce
    @0
    cA
    @3
    cmul
    oveq2
    fveq2d
    oveq12d
    oveq1d
    vx
    df-cos
    @11
    c2
    cdiv
    ovex
    fvmpt
end
