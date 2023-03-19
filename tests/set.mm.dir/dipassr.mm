include "ccphlo.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "3anrot.mm"
include "dipass.mm"
include "sylan2b.mm"
include "fveq2d.mm"
include "cnv.mm"
include "phnv.mm"
include "simpl.mm"
include "nvscl.mm"
include "3adant3r1.mm"
include "simpr1.mm"
include "dipcj.mm"
include "syl3anc.mm"
include "sylan.mm"
include "simpr2.mm"
include "dipcl.mm"
include "3com23.mm"
include "3adant3r2.mm"
include "cjmuld.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem dipassr
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cX: class X
  assume ipass.1: |- X = ( BaseSet ` U )
  assume ipass.4: |- S = ( .sOLD ` U )
  assume ipass.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. CC /\ C e. X ) ) -> ( A P ( B S C ) ) = ( ( * ` B ) x. ( A P C ) ) )

  proof
    cU
    ccphlo
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cc
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
    cB
    cC
    cS
    co
    #
    cA
    cP
    co
    #
    ccj
    cfv
    #
    cB
    cC
    cA
    cP
    co
    #
    cmul
    co
    #
    ccj
    cfv
    #
    cA
    @6
    cP
    co
    #
    cB
    ccj
    cfv
    #
    cA
    cC
    cP
    co
    #
    cmul
    co
    #
    @5
    @7
    @10
    ccj
    @4
    @0
    @2
    @3
    @1
    w3a
    @7
    @10
    wceq
    @1
    @2
    @3
    3anrot
    cB
    cC
    cA
    cP
    cS
    cU
    cX
    ipass.1
    ipass.4
    ipass.7
    dipass
    sylan2b
    fveq2d
    @0
    cU
    cnv
    wcel
    #
    @4
    @8
    @12
    wceq
    #
    cU
    phnv
    #
    @16
    @4
    wa
    #
    @16
    @6
    cX
    wcel
    #
    @1
    @17
    @16
    @4
    simpl
    @16
    @2
    @3
    @20
    @1
    cB
    cC
    cS
    cU
    cX
    ipass.1
    ipass.4
    nvscl
    3adant3r1
    @16
    @1
    @2
    @3
    simpr1
    @6
    cA
    cP
    cU
    cX
    ipass.1
    ipass.7
    dipcj
    syl3anc
    sylan
    @0
    @16
    @4
    @11
    @15
    wceq
    @18
    @19
    @11
    @13
    @9
    ccj
    cfv
    #
    cmul
    co
    @15
    @19
    cB
    @9
    @16
    @1
    @2
    @3
    simpr2
    @16
    @1
    @3
    @9
    cc
    wcel
    #
    @2
    @16
    @3
    @1
    @22
    cC
    cA
    cP
    cU
    cX
    ipass.1
    ipass.7
    dipcl
    3com23
    3adant3r2
    cjmuld
    @19
    @21
    @14
    @13
    cmul
    @16
    @1
    @3
    @21
    @14
    wceq
    #
    @2
    @16
    @3
    @1
    @23
    cC
    cA
    cP
    cU
    cX
    ipass.1
    ipass.7
    dipcj
    3com23
    3adant3r2
    oveq2d
    eqtrd
    sylan
    3eqtr3d
end
