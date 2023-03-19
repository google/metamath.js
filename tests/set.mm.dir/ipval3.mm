include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "cmin.mm"
include "ci.mm"
include "cmul.mm"
include "caddc.mm"
include "c4.mm"
include "cdiv.mm"
include "ipval2.mm"
include "nvmval.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "wceq.mm"
include "cc.mm"
include "ax-icn.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "3adant2.mm"
include "syld3an3.mm"
include "wa.mm"
include "mulm1i.mm"
include "oveq1i.mm"
include "neg1cn.mm"
include "nvsass.mm"
include "mp3anr1.mm"
include "mpanr1.mm"
include "syl5reqr.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eqtr4d.mm"

theorem ipval3
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume dipfval.1: |- X = ( BaseSet ` U )
  assume dipfval.2: |- G = ( +v ` U )
  assume dipfval.4: |- S = ( .sOLD ` U )
  assume dipfval.6: |- N = ( normCV ` U )
  assume dipfval.7: |- P = ( .iOLD ` U )
  assume ipval3.3: |- M = ( -v ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B ) = ( ( ( ( ( N ` ( A G B ) ) ^ 2 ) - ( ( N ` ( A M B ) ) ^ 2 ) ) + ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) - ( ( N ` ( A M ( _i S B ) ) ) ^ 2 ) ) ) ) / 4 ) )

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
    w3a
    #
    cA
    cB
    cP
    co
    cA
    cB
    cG
    co
    cN
    cfv
    c2
    cexp
    co
    #
    cA
    c1
    cneg
    #
    cB
    cS
    co
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
    cmin
    co
    #
    ci
    cA
    ci
    cB
    cS
    co
    #
    cG
    co
    cN
    cfv
    c2
    cexp
    co
    #
    cA
    ci
    cneg
    #
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
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    @4
    cA
    cB
    cM
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    ci
    @11
    cA
    @10
    cM
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    cA
    cB
    cP
    cS
    cU
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    ipval2
    @3
    @29
    @19
    c4
    cdiv
    @3
    @23
    @9
    @28
    @18
    caddc
    @3
    @22
    @8
    @4
    cmin
    @3
    @21
    @7
    c2
    cexp
    @3
    @20
    @6
    cN
    cA
    cB
    cS
    cU
    cG
    cM
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    ipval3.3
    nvmval
    fveq2d
    oveq1d
    oveq2d
    @3
    @27
    @17
    ci
    cmul
    @3
    @26
    @16
    @11
    cmin
    @3
    @25
    @15
    c2
    cexp
    @3
    @24
    @14
    cN
    @3
    @24
    cA
    @5
    @10
    cS
    co
    #
    cG
    co
    #
    @14
    @0
    @1
    @2
    @10
    cX
    wcel
    #
    @24
    @31
    wceq
    @0
    @2
    @32
    @1
    @0
    ci
    cc
    wcel
    #
    @2
    @32
    ax-icn
    ci
    cB
    cS
    cU
    cX
    dipfval.1
    dipfval.4
    nvscl
    mp3an2
    3adant2
    cA
    @10
    cS
    cU
    cG
    cM
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    ipval3.3
    nvmval
    syld3an3
    @3
    @30
    @13
    cA
    cG
    @0
    @2
    @30
    @13
    wceq
    @1
    @0
    @2
    wa
    @13
    @5
    ci
    cmul
    co
    #
    cB
    cS
    co
    #
    @30
    @34
    @12
    cB
    cS
    ci
    ax-icn
    mulm1i
    oveq1i
    @0
    @33
    @2
    @35
    @30
    wceq
    #
    ax-icn
    @0
    @5
    cc
    wcel
    @33
    @2
    @36
    neg1cn
    @5
    ci
    cB
    cS
    cU
    cX
    dipfval.1
    dipfval.4
    nvsass
    mp3anr1
    mpanr1
    syl5reqr
    3adant2
    oveq2d
    eqtrd
    fveq2d
    oveq1d
    oveq2d
    oveq2d
    oveq12d
    oveq1d
    eqtr4d
end
