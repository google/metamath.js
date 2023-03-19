include "cnv.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cpv.mm"
include "cfv.mm"
include "wceq.mm"
include "simpr1.mm"
include "simpr2.mm"
include "neg1cn.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "3ad2antr3.mm"
include "3jca.mm"
include "eqid.mm"
include "nvdi.mm"
include "syldan.mm"
include "nvscom.mm"
include "mp3anr2.mm"
include "3adantr2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "nvmval.mm"
include "3adant3r1.mm"
include "simpl.mm"
include "3adant3r3.mm"
include "3adant3r2.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"

theorem nvmdi
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cM: class M
  let cX: class X
  assume nvmdi.1: |- X = ( BaseSet ` U )
  assume nvmdi.3: |- M = ( -v ` U )
  assume nvmdi.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. X /\ C e. X ) ) -> ( A S ( B M C ) ) = ( ( A S B ) M ( A S C ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    c1
    cneg
    #
    cC
    cS
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cS
    co
    #
    cA
    cB
    cS
    co
    #
    @6
    cA
    cC
    cS
    co
    #
    cS
    co
    #
    @8
    co
    #
    cA
    cB
    cC
    cM
    co
    #
    cS
    co
    @11
    @12
    cM
    co
    #
    @5
    @10
    @11
    cA
    @7
    cS
    co
    #
    @8
    co
    #
    @14
    @0
    @4
    @1
    @2
    @7
    cX
    wcel
    #
    w3a
    @10
    @18
    wceq
    @5
    @1
    @2
    @19
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @3
    @19
    @2
    @0
    @6
    cc
    wcel
    #
    @3
    @19
    neg1cn
    @6
    cC
    cS
    cU
    cX
    nvmdi.1
    nvmdi.4
    nvscl
    mp3an2
    3ad2antr3
    3jca
    cA
    cB
    @7
    cS
    cU
    @8
    cX
    nvmdi.1
    @8
    eqid
    #
    nvmdi.4
    nvdi
    syldan
    @5
    @17
    @13
    @11
    @8
    @0
    @1
    @3
    @17
    @13
    wceq
    #
    @2
    @0
    @1
    @20
    @3
    @22
    neg1cn
    cA
    @6
    cC
    cS
    cU
    cX
    nvmdi.1
    nvmdi.4
    nvscom
    mp3anr2
    3adantr2
    oveq2d
    eqtrd
    @5
    @15
    @9
    cA
    cS
    @0
    @2
    @3
    @15
    @9
    wceq
    @1
    cB
    cC
    cS
    cU
    @8
    cM
    cX
    nvmdi.1
    @21
    nvmdi.4
    nvmdi.3
    nvmval
    3adant3r1
    oveq2d
    @5
    @0
    @11
    cX
    wcel
    #
    @12
    cX
    wcel
    #
    @16
    @14
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @23
    @3
    cA
    cB
    cS
    cU
    cX
    nvmdi.1
    nvmdi.4
    nvscl
    3adant3r3
    @0
    @1
    @3
    @24
    @2
    cA
    cC
    cS
    cU
    cX
    nvmdi.1
    nvmdi.4
    nvscl
    3adant3r2
    @11
    @12
    cS
    cU
    @8
    cM
    cX
    nvmdi.1
    @21
    nvmdi.4
    nvmdi.3
    nvmval
    syl3anc
    3eqtr4d
end
