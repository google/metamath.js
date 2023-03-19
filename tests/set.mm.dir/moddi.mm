include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmo.mm"
include "cc.mm"
include "rpcn.mm"
include "3ad2ant1.mm"
include "recn.mm"
include "3ad2ant2.mm"
include "wa.mm"
include "rpre.mm"
include "adantl.mm"
include "refldivcl.mm"
include "remulcld.mm"
include "recnd.mm"
include "3adant1.mm"
include "subdid.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "rpcnne0.mm"
include "3ad2ant3.mm"
include "divcan5.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "rerpdivcl.mm"
include "reflcl.mm"
include "syl.mm"
include "mulassd.mm"
include "eqtr2d.mm"
include "eqtrd.mm"
include "modval.mm"
include "remulcl.mm"
include "sylan.mm"
include "3adant3.mm"
include "rpmulcl.mm"
include "3adant2.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"

theorem moddi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR+ /\ B e. RR /\ C e. RR+ ) -> ( A x. ( B mod C ) ) = ( ( A x. B ) mod ( A x. C ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    crp
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cB
    cC
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    cA
    cB
    cmul
    co
    #
    cA
    cC
    cmul
    co
    #
    @9
    @10
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cA
    cB
    cC
    cmo
    co
    #
    cmul
    co
    @9
    @10
    cmo
    co
    #
    @3
    @8
    @9
    cA
    @6
    cmul
    co
    #
    cmin
    co
    @14
    @3
    cA
    cB
    @6
    @0
    @1
    cA
    cc
    wcel
    #
    @2
    cA
    rpcn
    3ad2ant1
    #
    @1
    @0
    cB
    cc
    wcel
    #
    @2
    cB
    recn
    3ad2ant2
    #
    @1
    @2
    @6
    cc
    wcel
    @0
    @1
    @2
    wa
    #
    @6
    @22
    cC
    @5
    @2
    cC
    cr
    wcel
    @1
    cC
    rpre
    adantl
    cB
    cC
    refldivcl
    remulcld
    recnd
    3adant1
    subdid
    @3
    @17
    @13
    @9
    cmin
    @3
    @13
    @10
    @5
    cmul
    co
    @17
    @3
    @12
    @5
    @10
    cmul
    @3
    @11
    @4
    cfl
    @3
    @20
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    wa
    #
    @18
    cA
    cc0
    wne
    wa
    #
    @11
    @4
    wceq
    @21
    @2
    @0
    @24
    @1
    cC
    rpcnne0
    3ad2ant3
    @0
    @1
    @25
    @2
    cA
    rpcnne0
    3ad2ant1
    cB
    cC
    cA
    divcan5
    syl3anc
    fveq2d
    oveq2d
    @3
    cA
    cC
    @5
    @19
    @2
    @0
    @23
    @1
    cC
    rpcn
    3ad2ant3
    @1
    @2
    @5
    cc
    wcel
    #
    @0
    @22
    @4
    cr
    wcel
    #
    @26
    cB
    cC
    rerpdivcl
    @27
    @5
    @4
    reflcl
    recnd
    syl
    3adant1
    mulassd
    eqtr2d
    oveq2d
    eqtrd
    @3
    @15
    @7
    cA
    cmul
    @1
    @2
    @15
    @7
    wceq
    @0
    cB
    cC
    modval
    3adant1
    oveq2d
    @3
    @9
    cr
    wcel
    #
    @10
    crp
    wcel
    #
    @16
    @14
    wceq
    @0
    @1
    @28
    @2
    @0
    cA
    cr
    wcel
    @1
    @28
    cA
    rpre
    cA
    cB
    remulcl
    sylan
    3adant3
    @0
    @2
    @29
    @1
    cA
    cC
    rpmulcl
    3adant2
    @9
    @10
    modval
    syl2anc
    3eqtr4d
end
