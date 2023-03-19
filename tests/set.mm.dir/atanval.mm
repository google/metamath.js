include "catan.mm"
include "cfv.mm"
include "ci.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "cmin.mm"
include "clog.mm"
include "caddc.mm"
include "wceq.mm"
include "cc.mm"
include "cneg.mm"
include "cpr.mm"
include "cdif.mm"
include "cdm.mm"
include "cv.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "df-atan.mm"
include "ovex.mm"
include "fvmpt.mm"
include "atanf.mm"
include "fdmi.mm"
include "eleq2s.mm"

theorem atanval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. dom arctan -> ( arctan ` A ) = ( ( _i / 2 ) x. ( ( log ` ( 1 - ( _i x. A ) ) ) - ( log ` ( 1 + ( _i x. A ) ) ) ) ) )

  proof
    cA
    catan
    cfv
    ci
    c2
    cdiv
    co
    #
    c1
    ci
    cA
    cmul
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    c1
    @1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    wceq
    cA
    cc
    ci
    cneg
    ci
    cpr
    cdif
    #
    catan
    cdm
    vx
    cA
    @0
    c1
    ci
    vx
    cv
    #
    cmul
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    c1
    @10
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    @7
    @8
    catan
    @9
    cA
    wceq
    #
    @15
    @6
    @0
    cmul
    @16
    @12
    @3
    @14
    @5
    cmin
    @16
    @11
    @2
    clog
    @16
    @10
    @1
    c1
    cmin
    @9
    cA
    ci
    cmul
    oveq2
    #
    oveq2d
    fveq2d
    @16
    @13
    @4
    clog
    @16
    @10
    @1
    c1
    caddc
    @17
    oveq2d
    fveq2d
    oveq12d
    oveq2d
    vx
    df-atan
    @0
    @6
    cmul
    ovex
    fvmpt
    @8
    cc
    catan
    atanf
    fdmi
    eleq2s
end
