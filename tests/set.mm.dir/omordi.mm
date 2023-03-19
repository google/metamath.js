include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "comu.mm"
include "co.mm"
include "wi.mm"
include "onelon.mm"
include "ex.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "eleq2.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "imbi12d.mm"
include "noel.mm"
include "pm2.21i.mm"
include "a1i.mm"
include "coa.mm"
include "wo.mm"
include "elsuci.mm"
include "omcl.mm"
include "simpl.mm"
include "jca.mm"
include "oaword1.mm"
include "sseld.mm"
include "imim2d.mm"
include "imp.mm"
include "adantrl.mm"
include "oaord1.mm"
include "biimpa.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "adantrr.mm"
include "jaod.mm"
include "sylan.mm"
include "syl5.mm"
include "wb.mm"
include "omsuc.mm"
include "adantr.mm"
include "sylibrd.mm"
include "exp43.mm"
include "com12.mm"
include "adantld.mm"
include "impd.mm"
include "wlim.mm"
include "wral.mm"
include "wss.mm"
include "id.mm"
include "ad2ant2r.mm"
include "ciun.mm"
include "limsuc.mm"
include "ssiun2s.mm"
include "syl.mm"
include "adantll.mm"
include "cvv.mm"
include "vex.mm"
include "omlim.mm"
include "mpanr1.mm"
include "sseqtr4d.mm"
include "anabss1.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "exp53.mm"
include "com13.mm"
include "imp4c.mm"
include "a1dd.mm"
include "tfinds3.mm"
include "com23.mm"
include "exp4a.mm"
include "mpdd.mm"
include "com34.mm"
include "com24.mm"
include "imp31.mm"

theorem omordi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( B e. On /\ C e. On ) /\ (/) e. C ) -> ( A e. B -> ( C .o A ) e. ( C .o B ) ) )

  proof
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    c0
    cC
    wcel
    #
    cA
    cB
    wcel
    #
    cC
    cA
    comu
    co
    #
    cC
    cB
    comu
    co
    #
    wcel
    #
    wi
    #
    @0
    @3
    @2
    @1
    @6
    @0
    @3
    @1
    @2
    @6
    @0
    @3
    cA
    con0
    wcel
    #
    @1
    @2
    @6
    wi
    #
    wi
    @0
    @3
    @8
    cB
    cA
    onelon
    ex
    @0
    @3
    @8
    @1
    @9
    @0
    @3
    @8
    @1
    wa
    #
    @2
    @6
    @0
    @10
    @2
    wa
    #
    @3
    @6
    cA
    vx
    cv
    #
    wcel
    #
    @4
    cC
    @12
    comu
    co
    #
    wcel
    #
    wi
    #
    cA
    c0
    wcel
    #
    @4
    cC
    c0
    comu
    co
    #
    wcel
    #
    wi
    #
    cA
    vy
    cv
    #
    wcel
    #
    @4
    cC
    @21
    comu
    co
    #
    wcel
    #
    wi
    #
    cA
    @21
    csuc
    #
    wcel
    #
    @4
    cC
    @26
    comu
    co
    #
    wcel
    #
    wi
    #
    @7
    @11
    vx
    vy
    cB
    @12
    c0
    wceq
    #
    @13
    @17
    @15
    @19
    @12
    c0
    cA
    eleq2
    @31
    @14
    @18
    @4
    @12
    c0
    cC
    comu
    oveq2
    eleq2d
    imbi12d
    @12
    @21
    wceq
    #
    @13
    @22
    @15
    @24
    @12
    @21
    cA
    eleq2
    @32
    @14
    @23
    @4
    @12
    @21
    cC
    comu
    oveq2
    eleq2d
    imbi12d
    @12
    @26
    wceq
    #
    @13
    @27
    @15
    @29
    @12
    @26
    cA
    eleq2
    @33
    @14
    @28
    @4
    @12
    @26
    cC
    comu
    oveq2
    eleq2d
    imbi12d
    @12
    cB
    wceq
    #
    @13
    @3
    @15
    @6
    @12
    cB
    cA
    eleq2
    @34
    @14
    @5
    @4
    @12
    cB
    cC
    comu
    oveq2
    eleq2d
    imbi12d
    @20
    @11
    @17
    @19
    cA
    noel
    pm2.21i
    a1i
    @21
    con0
    wcel
    #
    @10
    @2
    @25
    @30
    wi
    #
    @35
    @1
    @2
    @36
    wi
    #
    @8
    @1
    @35
    @37
    @1
    @35
    @2
    @25
    @30
    @1
    @35
    wa
    #
    @2
    @25
    wa
    #
    wa
    #
    @27
    @4
    @23
    cC
    coa
    co
    #
    wcel
    #
    @29
    @27
    @22
    cA
    @21
    wceq
    #
    wo
    #
    @40
    @42
    cA
    @21
    elsuci
    @38
    @23
    con0
    wcel
    #
    @1
    wa
    #
    @39
    @44
    @42
    wi
    @38
    @45
    @1
    cC
    @21
    omcl
    @1
    @35
    simpl
    jca
    @46
    @39
    wa
    @22
    @42
    @43
    @46
    @25
    @22
    @42
    wi
    #
    @2
    @46
    @25
    @47
    @46
    @24
    @42
    @22
    @46
    @23
    @41
    @4
    @23
    cC
    oaword1
    sseld
    imim2d
    imp
    adantrl
    @46
    @2
    @43
    @42
    wi
    @25
    @46
    @2
    wa
    @42
    @43
    @23
    @41
    wcel
    #
    @46
    @2
    @48
    @23
    cC
    oaord1
    biimpa
    @43
    @4
    @23
    @41
    cA
    @21
    cC
    comu
    oveq2
    eleq1d
    syl5ibrcom
    adantrr
    jaod
    sylan
    syl5
    @38
    @29
    @42
    wb
    @39
    @38
    @28
    @41
    @4
    cC
    @21
    omsuc
    eleq2d
    adantr
    sylibrd
    exp43
    com12
    adantld
    impd
    @12
    wlim
    #
    @11
    @16
    @25
    vy
    @12
    wral
    @49
    @8
    @1
    @2
    @16
    @1
    @8
    @49
    @2
    @16
    wi
    @1
    @8
    @49
    @2
    @13
    @15
    @1
    @8
    wa
    #
    @49
    @2
    wa
    wa
    #
    @13
    wa
    cC
    cA
    csuc
    #
    comu
    co
    #
    @14
    @4
    @51
    @1
    @49
    wa
    #
    @13
    @53
    @14
    wss
    @1
    @49
    @54
    @8
    @2
    @54
    id
    ad2ant2r
    @54
    @13
    wa
    @53
    vy
    @12
    @23
    ciun
    #
    @14
    @49
    @13
    @53
    @55
    wss
    #
    @1
    @49
    @13
    wa
    @52
    @12
    wcel
    #
    @56
    @49
    @13
    @57
    @12
    cA
    limsuc
    biimpa
    vy
    @12
    @23
    @52
    @53
    @21
    @52
    cC
    comu
    oveq2
    ssiun2s
    syl
    adantll
    @54
    @14
    @55
    wceq
    #
    @13
    @1
    @12
    cvv
    wcel
    @49
    @58
    vx
    vex
    vy
    cC
    @12
    cvv
    omlim
    mpanr1
    adantr
    sseqtr4d
    sylan
    @51
    @4
    @53
    wcel
    #
    @13
    @50
    @2
    @59
    @49
    @50
    @2
    wa
    @4
    @4
    cC
    coa
    co
    #
    @53
    @50
    @2
    @4
    @60
    wcel
    #
    @1
    @8
    @2
    @61
    wb
    #
    @50
    @4
    con0
    wcel
    @1
    @62
    cC
    cA
    omcl
    @4
    cC
    oaord1
    sylan
    anabss1
    biimpa
    @50
    @53
    @60
    wceq
    @2
    cC
    cA
    omsuc
    adantr
    eleqtrrd
    adantrl
    adantr
    sseldd
    exp53
    com13
    imp4c
    a1dd
    tfinds3
    com23
    exp4a
    exp4a
    mpdd
    com34
    com24
    imp31
end
