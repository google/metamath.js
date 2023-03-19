include "cnv.mm"
include "wcel.mm"
include "cdip.mm"
include "cfv.mm"
include "c1.mm"
include "c4.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "c2.mm"
include "cmul.mm"
include "csu.mm"
include "cdiv.mm"
include "cmpt2.mm"
include "cba.mm"
include "cns.mm"
include "cpv.mm"
include "cnmcv.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "fveq12d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "mpt2eq123dv.mm"
include "df-dip.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl5eq.mm"

theorem dipfval
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cS: class S
  let cU: class U
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cX: class X
  let vu: setvar u
  let cA: class A
  let cB: class B
  assume dipfval.1: |- X = ( BaseSet ` U )
  assume dipfval.2: |- G = ( +v ` U )
  assume dipfval.4: |- S = ( .sOLD ` U )
  assume dipfval.6: |- N = ( normCV ` U )
  assume dipfval.7: |- P = ( .iOLD ` U )

  disjoint k x
  disjoint k y
  disjoint G k
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint U k
  disjoint U x
  disjoint U y
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint k u
  disjoint u x
  disjoint u y
  disjoint G u
  disjoint N u
  disjoint S u
  disjoint U u
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint X u
  assert |- ( U e. NrmCVec -> P = ( x e. X , y e. X |-> ( sum_ k e. ( 1 ... 4 ) ( ( _i ^ k ) x. ( ( N ` ( x G ( ( _i ^ k ) S y ) ) ) ^ 2 ) ) / 4 ) ) )

  proof
    cU
    cnv
    wcel
    cP
    cU
    cdip
    cfv
    vx
    vy
    cX
    cX
    c1
    c4
    cfz
    co
    #
    ci
    vk
    cv
    cexp
    co
    #
    vx
    cv
    #
    @1
    vy
    cv
    #
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    c4
    cdiv
    co
    #
    cmpt2
    #
    dipfval.7
    vu
    cU
    vx
    vy
    vu
    cv
    #
    cba
    cfv
    #
    @13
    @0
    @1
    @2
    @1
    @3
    @12
    cns
    cfv
    #
    co
    #
    @12
    cpv
    cfv
    #
    co
    #
    @12
    cnmcv
    cfv
    #
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    c4
    cdiv
    co
    #
    cmpt2
    @11
    cnv
    cdip
    @12
    cU
    wceq
    #
    vx
    vy
    @13
    @13
    @23
    cX
    cX
    @10
    @24
    @13
    cU
    cba
    cfv
    #
    cX
    @12
    cU
    cba
    fveq2
    dipfval.1
    syl6eqr
    #
    @26
    @24
    @22
    @9
    c4
    cdiv
    @24
    @0
    @21
    @8
    vk
    @24
    @20
    @7
    @1
    cmul
    @24
    @19
    @6
    c2
    cexp
    @24
    @17
    @5
    @18
    cN
    @24
    @18
    cU
    cnmcv
    cfv
    cN
    @12
    cU
    cnmcv
    fveq2
    dipfval.6
    syl6eqr
    @24
    @2
    @2
    @15
    @4
    @16
    cG
    @24
    @16
    cU
    cpv
    cfv
    cG
    @12
    cU
    cpv
    fveq2
    dipfval.2
    syl6eqr
    @24
    @2
    eqidd
    @24
    @14
    cS
    @1
    @3
    @24
    @14
    cU
    cns
    cfv
    cS
    @12
    cU
    cns
    fveq2
    dipfval.4
    syl6eqr
    oveqd
    oveq123d
    fveq12d
    oveq1d
    oveq2d
    sumeq2sdv
    oveq1d
    mpt2eq123dv
    vx
    vy
    vu
    vk
    df-dip
    vx
    vy
    cX
    cX
    @10
    cX
    @25
    cvv
    dipfval.1
    cU
    cba
    fvex
    eqeltri
    #
    @27
    mpt2ex
    fvmpt
    syl5eq
end
