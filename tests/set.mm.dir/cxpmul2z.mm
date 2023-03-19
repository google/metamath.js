include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cz.mm"
include "cmul.mm"
include "co.mm"
include "ccxp.mm"
include "cexp.mm"
include "wceq.mm"
include "cr.mm"
include "cn0.mm"
include "cneg.mm"
include "wo.mm"
include "elznn0.mm"
include "wi.mm"
include "cxpmul2.mm"
include "3expia.mm"
include "adantlr.mm"
include "adantr.mm"
include "c1.mm"
include "cdiv.mm"
include "simplll.mm"
include "simplr.mm"
include "simprr.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "simprl.mm"
include "recnd.mm"
include "mulneg2d.mm"
include "negeqd.mm"
include "mulcld.mm"
include "negnegd.mm"
include "eqtrd.mm"
include "simpllr.mm"
include "negcld.mm"
include "cxpneg.mm"
include "eqtr3d.mm"
include "cxpcl.mm"
include "syl2anc.mm"
include "expneg2.mm"
include "3eqtr4d.mm"
include "expr.mm"
include "jaod.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "impr.mm"

theorem cxpmul2z
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ C e. ZZ ) ) -> ( A ^c ( B x. C ) ) = ( ( A ^c B ) ^ C ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cc
    wcel
    #
    cC
    cz
    wcel
    #
    cA
    cB
    cC
    cmul
    co
    #
    ccxp
    co
    #
    cA
    cB
    ccxp
    co
    #
    cC
    cexp
    co
    #
    wceq
    #
    @4
    cC
    cr
    wcel
    #
    cC
    cn0
    wcel
    #
    cC
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    wa
    @2
    @3
    wa
    #
    @9
    cC
    elznn0
    @15
    @10
    @14
    @9
    @15
    @10
    wa
    @11
    @9
    @13
    @15
    @11
    @9
    wi
    #
    @10
    @0
    @3
    @16
    @1
    @0
    @3
    @11
    @9
    cA
    cB
    cC
    cxpmul2
    3expia
    adantlr
    adantr
    @15
    @10
    @13
    @9
    @15
    @10
    @13
    wa
    #
    wa
    #
    c1
    cA
    cB
    @12
    cmul
    co
    #
    ccxp
    co
    #
    cdiv
    co
    #
    c1
    @7
    @12
    cexp
    co
    #
    cdiv
    co
    #
    @6
    @8
    @18
    @20
    @22
    c1
    cdiv
    @18
    @0
    @3
    @13
    @20
    @22
    wceq
    @0
    @1
    @3
    @17
    simplll
    #
    @2
    @3
    @17
    simplr
    #
    @15
    @10
    @13
    simprr
    #
    cA
    cB
    @12
    cxpmul2
    syl3anc
    oveq2d
    @18
    cA
    @19
    cneg
    #
    ccxp
    co
    #
    @6
    @21
    @18
    @27
    @5
    cA
    ccxp
    @18
    @27
    @5
    cneg
    #
    cneg
    @5
    @18
    @19
    @29
    @18
    cB
    cC
    @25
    @18
    cC
    @15
    @10
    @13
    simprl
    recnd
    #
    mulneg2d
    negeqd
    @18
    @5
    @18
    cB
    cC
    @25
    @30
    mulcld
    negnegd
    eqtrd
    oveq2d
    @18
    @0
    @1
    @19
    cc
    wcel
    @28
    @21
    wceq
    @24
    @0
    @1
    @3
    @17
    simpllr
    @18
    cB
    @12
    @25
    @18
    cC
    @30
    negcld
    mulcld
    cA
    @19
    cxpneg
    syl3anc
    eqtr3d
    @18
    @7
    cc
    wcel
    #
    cC
    cc
    wcel
    @13
    @8
    @23
    wceq
    @18
    @0
    @3
    @31
    @24
    @25
    cA
    cB
    cxpcl
    syl2anc
    @30
    @26
    @7
    cC
    expneg2
    syl3anc
    3eqtr4d
    expr
    jaod
    expimpd
    syl5bi
    impr
end
