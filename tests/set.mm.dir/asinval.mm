include "ci.mm"
include "cneg.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "clog.mm"
include "cc.mm"
include "casin.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "df-asin.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem asinval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. CC -> ( arcsin ` A ) = ( -u _i x. ( log ` ( ( _i x. A ) + ( sqrt ` ( 1 - ( A ^ 2 ) ) ) ) ) ) )

  proof
    vx
    cA
    ci
    cneg
    #
    ci
    vx
    cv
    #
    cmul
    co
    #
    c1
    @1
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    clog
    cfv
    #
    cmul
    co
    @0
    ci
    cA
    cmul
    co
    #
    c1
    cA
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    clog
    cfv
    #
    cmul
    co
    cc
    casin
    @1
    cA
    wceq
    #
    @7
    @13
    @0
    cmul
    @14
    @6
    @12
    clog
    @14
    @2
    @8
    @5
    @11
    caddc
    @1
    cA
    ci
    cmul
    oveq2
    @14
    @4
    @10
    csqrt
    @14
    @3
    @9
    c1
    cmin
    @1
    cA
    c2
    cexp
    oveq1
    oveq2d
    fveq2d
    oveq12d
    fveq2d
    oveq2d
    vx
    df-asin
    @0
    @13
    cmul
    ovex
    fvmpt
end
