include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "cc.mm"
include "csin.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "df-sin.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem sinval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. CC -> ( sin ` A ) = ( ( ( exp ` ( _i x. A ) ) - ( exp ` ( -u _i x. A ) ) ) / ( 2 x. _i ) ) )

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
    cmin
    co
    #
    c2
    ci
    cmul
    co
    #
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
    cmin
    co
    #
    @7
    cdiv
    co
    cc
    csin
    @0
    cA
    wceq
    #
    @6
    @12
    @7
    cdiv
    @13
    @2
    @9
    @5
    @11
    cmin
    @13
    @1
    @8
    ce
    @0
    cA
    ci
    cmul
    oveq2
    fveq2d
    @13
    @4
    @10
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
    df-sin
    @12
    @7
    cdiv
    ovex
    fvmpt
end
