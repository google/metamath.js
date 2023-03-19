include "wcel.mm"
include "w3a.mm"
include "ccphlo.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "id.mm"
include "3com13.mm"
include "wa.mm"
include "ccj.mm"
include "cfv.mm"
include "3com12.mm"
include "dipdir.mm"
include "sylan2.mm"
include "fveq2d.mm"
include "cnv.mm"
include "phnv.mm"
include "simpl.mm"
include "nvgcl.mm"
include "3com23.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "dipcj.mm"
include "syl3anc.mm"
include "sylan.mm"
include "cc.mm"
include "dipcl.mm"
include "3adant3r1.mm"
include "3adant3r2.mm"
include "cjaddd.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem dipdi
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cU: class U
  let cG: class G
  let cX: class X
  assume dipdir.1: |- X = ( BaseSet ` U )
  assume dipdir.2: |- G = ( +v ` U )
  assume dipdir.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A P ( B G C ) ) = ( ( A P B ) + ( A P C ) ) )

  proof
    cA
    cX
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
    cU
    ccphlo
    wcel
    #
    @2
    @1
    @0
    w3a
    #
    cA
    cB
    cC
    cG
    co
    #
    cP
    co
    #
    cA
    cB
    cP
    co
    #
    cA
    cC
    cP
    co
    #
    caddc
    co
    #
    wceq
    @2
    @1
    @0
    @4
    @4
    id
    3com13
    @3
    @4
    wa
    #
    @5
    cA
    cP
    co
    #
    ccj
    cfv
    #
    cB
    cA
    cP
    co
    #
    cC
    cA
    cP
    co
    #
    caddc
    co
    #
    ccj
    cfv
    #
    @6
    @9
    @10
    @11
    @15
    ccj
    @4
    @3
    @1
    @2
    @0
    w3a
    #
    @11
    @15
    wceq
    @1
    @2
    @0
    @17
    @17
    id
    3com12
    cB
    cC
    cA
    cP
    cU
    cG
    cX
    dipdir.1
    dipdir.2
    dipdir.7
    dipdir
    sylan2
    fveq2d
    @3
    cU
    cnv
    wcel
    #
    @4
    @12
    @6
    wceq
    #
    cU
    phnv
    #
    @18
    @4
    wa
    #
    @18
    @5
    cX
    wcel
    #
    @0
    @19
    @18
    @4
    simpl
    @18
    @2
    @1
    @22
    @0
    @18
    @1
    @2
    @22
    cB
    cC
    cU
    cG
    cX
    dipdir.1
    dipdir.2
    nvgcl
    3com23
    3adant3r3
    @18
    @2
    @1
    @0
    simpr3
    @5
    cA
    cP
    cU
    cX
    dipdir.1
    dipdir.7
    dipcj
    syl3anc
    sylan
    @3
    @18
    @4
    @16
    @9
    wceq
    @20
    @21
    @16
    @13
    ccj
    cfv
    #
    @14
    ccj
    cfv
    #
    caddc
    co
    @9
    @21
    @13
    @14
    @18
    @1
    @0
    @13
    cc
    wcel
    @2
    cB
    cA
    cP
    cU
    cX
    dipdir.1
    dipdir.7
    dipcl
    3adant3r1
    @18
    @2
    @0
    @14
    cc
    wcel
    @1
    cC
    cA
    cP
    cU
    cX
    dipdir.1
    dipdir.7
    dipcl
    3adant3r2
    cjaddd
    @21
    @23
    @7
    @24
    @8
    caddc
    @18
    @1
    @0
    @23
    @7
    wceq
    @2
    cB
    cA
    cP
    cU
    cX
    dipdir.1
    dipdir.7
    dipcj
    3adant3r1
    @18
    @2
    @0
    @24
    @8
    wceq
    @1
    cC
    cA
    cP
    cU
    cX
    dipdir.1
    dipdir.7
    dipcj
    3adant3r2
    oveq12d
    eqtrd
    sylan
    3eqtr3d
    sylan2
end
