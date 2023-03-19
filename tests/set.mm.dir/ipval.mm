include "cnv.mm"
include "wcel.mm"
include "co.mm"
include "c1.mm"
include "c4.mm"
include "cfz.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cfv.mm"
include "c2.mm"
include "cmul.mm"
include "csu.mm"
include "cdiv.mm"
include "wceq.mm"
include "wa.mm"
include "cmpt2.mm"
include "dipfval.mm"
include "oveqd.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "sylan9eq.mm"
include "3impb.mm"

theorem ipval
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cX: class X
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume dipfval.1: |- X = ( BaseSet ` U )
  assume dipfval.2: |- G = ( +v ` U )
  assume dipfval.4: |- S = ( .sOLD ` U )
  assume dipfval.6: |- N = ( normCV ` U )
  assume dipfval.7: |- P = ( .iOLD ` U )

  disjoint G k
  disjoint N k
  disjoint S k
  disjoint U k
  disjoint A k
  disjoint B k
  disjoint X k
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint u x
  disjoint u y
  disjoint G u
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint U u
  disjoint U x
  disjoint U y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint X u
  disjoint X x
  disjoint X y
  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B ) = ( sum_ k e. ( 1 ... 4 ) ( ( _i ^ k ) x. ( ( N ` ( A G ( ( _i ^ k ) S B ) ) ) ^ 2 ) ) / 4 ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cP
    co
    #
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
    cA
    @5
    cB
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
    wceq
    @0
    @1
    @2
    wa
    @3
    cA
    cB
    vx
    vy
    cX
    cX
    @4
    @5
    vx
    cv
    #
    @5
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
    co
    @12
    @0
    cP
    @22
    cA
    cB
    vx
    vy
    cP
    cS
    cU
    vk
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    dipfval
    oveqd
    vx
    vy
    cA
    cB
    cX
    cX
    @21
    @12
    @22
    @4
    @5
    cA
    @15
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
    @13
    cA
    wceq
    #
    @20
    @27
    c4
    cdiv
    @28
    @4
    @19
    @26
    vk
    @28
    @18
    @25
    @5
    cmul
    @28
    @17
    @24
    c2
    cexp
    @28
    @16
    @23
    cN
    @13
    cA
    @15
    cG
    oveq1
    fveq2d
    oveq1d
    oveq2d
    sumeq2sdv
    oveq1d
    @14
    cB
    wceq
    #
    @27
    @11
    c4
    cdiv
    @29
    @4
    @26
    @10
    vk
    @29
    @25
    @9
    @5
    cmul
    @29
    @24
    @8
    c2
    cexp
    @29
    @23
    @7
    cN
    @29
    @15
    @6
    cA
    cG
    @14
    cB
    @5
    cS
    oveq2
    oveq2d
    fveq2d
    oveq1d
    oveq2d
    sumeq2sdv
    oveq1d
    @22
    eqid
    @11
    c4
    cdiv
    ovex
    ovmpt2
    sylan9eq
    3impb
end
