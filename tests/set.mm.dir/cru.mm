include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "simplrl.mm"
include "recnd.mm"
include "simplll.mm"
include "cmin.mm"
include "cc0.mm"
include "simpr.mm"
include "cc.mm"
include "ax-icn.mm"
include "a1i.mm"
include "simpllr.mm"
include "mulcld.mm"
include "simplrr.mm"
include "addsubeq4d.mm"
include "mpbid.mm"
include "resubcld.mm"
include "subdid.mm"
include "eqtr4d.mm"
include "eqeltrd.mm"
include "rimul.mm"
include "syl2anc.mm"
include "subeq0d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "subidd.mm"
include "3eqtrd.mm"
include "eqcomd.mm"
include "jca.mm"
include "ex.mm"
include "oveq2.mm"
include "oveq12.mm"
include "sylan2.mm"
include "impbid1.mm"

theorem cru
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( A + ( _i x. B ) ) = ( C + ( _i x. D ) ) <-> ( A = C /\ B = D ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    #
    wa
    #
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    cC
    ci
    cD
    cmul
    co
    #
    caddc
    co
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    #
    @6
    @9
    @12
    @6
    @9
    wa
    #
    @10
    @11
    @13
    cC
    cA
    @13
    cC
    cA
    @13
    cC
    @2
    @3
    @4
    @9
    simplrl
    #
    recnd
    #
    @13
    cA
    @0
    @1
    @5
    @9
    simplll
    #
    recnd
    #
    @13
    cC
    cA
    cmin
    co
    #
    @7
    @8
    cmin
    co
    #
    @8
    @8
    cmin
    co
    cc0
    @13
    @9
    @18
    @19
    wceq
    @6
    @9
    simpr
    @13
    cA
    @7
    cC
    @8
    @17
    @13
    ci
    cB
    ci
    cc
    wcel
    @13
    ax-icn
    a1i
    #
    @13
    cB
    @0
    @1
    @5
    @9
    simpllr
    #
    recnd
    #
    mulcld
    @15
    @13
    ci
    cD
    @20
    @13
    cD
    @2
    @3
    @4
    @9
    simplrr
    #
    recnd
    #
    mulcld
    #
    addsubeq4d
    mpbid
    #
    @13
    @7
    @8
    @8
    cmin
    @13
    cB
    cD
    ci
    cmul
    @13
    cB
    cD
    @22
    @24
    @13
    cB
    cD
    cmin
    co
    #
    cr
    wcel
    ci
    @27
    cmul
    co
    #
    cr
    wcel
    @27
    cc0
    wceq
    @13
    cB
    cD
    @21
    @23
    resubcld
    @13
    @28
    @18
    cr
    @13
    @28
    @19
    @18
    @13
    ci
    cB
    cD
    @20
    @22
    @24
    subdid
    @26
    eqtr4d
    @13
    cC
    cA
    @14
    @16
    resubcld
    eqeltrd
    @27
    rimul
    syl2anc
    subeq0d
    #
    oveq2d
    oveq1d
    @13
    @8
    @25
    subidd
    3eqtrd
    subeq0d
    eqcomd
    @29
    jca
    ex
    @11
    @10
    @7
    @8
    wceq
    @9
    cB
    cD
    ci
    cmul
    oveq2
    cA
    cC
    @7
    @8
    caddc
    oveq12
    sylan2
    impbid1
end
