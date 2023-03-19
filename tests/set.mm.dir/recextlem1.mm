include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "cneg.mm"
include "simpl.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "adantl.mm"
include "subcl.mm"
include "sylan2.mm"
include "adddird.mm"
include "subdid.mm"
include "wceq.mm"
include "mulcom.mm"
include "c1.mm"
include "ixi.mm"
include "oveq1i.mm"
include "mulm1d.mm"
include "syl5req.mm"
include "mul4.mm"
include "mpanl12.mm"
include "eqtrd.mm"
include "anidms.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "negcld.mm"
include "npncand.mm"
include "subneg.mm"
include "syl2an.mm"
include "3eqtrd.mm"

theorem recextlem1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A + ( _i x. B ) ) x. ( A - ( _i x. B ) ) ) = ( ( A x. A ) + ( B x. B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
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
    cA
    @3
    cmin
    co
    #
    cmul
    co
    cA
    @4
    cmul
    co
    #
    @3
    @4
    cmul
    co
    #
    caddc
    co
    cA
    cA
    cmul
    co
    #
    cA
    @3
    cmul
    co
    #
    cmin
    co
    #
    @8
    cB
    cB
    cmul
    co
    #
    cneg
    #
    cmin
    co
    #
    caddc
    co
    #
    @7
    @10
    caddc
    co
    #
    @2
    cA
    @3
    @4
    @0
    @1
    simpl
    #
    @1
    @3
    cc
    wcel
    #
    @0
    ci
    cc
    wcel
    #
    @1
    @16
    ax-icn
    ci
    cB
    mulcl
    mpan
    #
    adantl
    #
    @1
    @0
    @16
    @4
    cc
    wcel
    @18
    cA
    @3
    subcl
    sylan2
    adddird
    @2
    @5
    @9
    @6
    @12
    caddc
    @2
    cA
    cA
    @3
    @15
    @15
    @19
    subdid
    @2
    @6
    @3
    cA
    cmul
    co
    #
    @3
    @3
    cmul
    co
    #
    cmin
    co
    @12
    @2
    @3
    cA
    @3
    @19
    @15
    @19
    subdid
    @2
    @8
    @20
    @11
    @21
    cmin
    @1
    @0
    @16
    @8
    @20
    wceq
    @18
    cA
    @3
    mulcom
    sylan2
    @1
    @11
    @21
    wceq
    #
    @0
    @1
    @22
    @1
    @1
    wa
    #
    @11
    ci
    ci
    cmul
    co
    #
    @10
    cmul
    co
    #
    @21
    @23
    @25
    c1
    cneg
    #
    @10
    cmul
    co
    @11
    @24
    @26
    @10
    cmul
    ixi
    oveq1i
    @23
    @10
    cB
    cB
    mulcl
    #
    mulm1d
    syl5req
    @17
    @17
    @23
    @25
    @21
    wceq
    ax-icn
    ax-icn
    ci
    ci
    cB
    cB
    mul4
    mpanl12
    eqtrd
    anidms
    adantl
    oveq12d
    eqtr4d
    oveq12d
    @2
    @13
    @7
    @11
    cmin
    co
    #
    @14
    @2
    @7
    @8
    @11
    @0
    @7
    cc
    wcel
    #
    @1
    @0
    @29
    cA
    cA
    mulcl
    anidms
    #
    adantr
    @1
    @0
    @16
    @8
    cc
    wcel
    @18
    cA
    @3
    mulcl
    sylan2
    @1
    @11
    cc
    wcel
    #
    @0
    @1
    @31
    @23
    @10
    @27
    negcld
    anidms
    adantl
    npncand
    @0
    @29
    @10
    cc
    wcel
    #
    @28
    @14
    wceq
    @1
    @30
    @1
    @32
    @27
    anidms
    @7
    @10
    subneg
    syl2an
    eqtrd
    3eqtrd
end
