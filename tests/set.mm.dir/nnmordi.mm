include "com.mm"
include "wcel.mm"
include "c0.mm"
include "comu.mm"
include "co.mm"
include "wi.mm"
include "elnn.mm"
include "expcom.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "eleq2.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "csuc.mm"
include "noel.mm"
include "pm2.21i.mm"
include "a1i.mm"
include "coa.mm"
include "wo.mm"
include "elsuci.mm"
include "nnmcl.mm"
include "simpl.mm"
include "jca.mm"
include "nnaword1.mm"
include "sseld.mm"
include "imim2d.mm"
include "imp.mm"
include "adantrl.mm"
include "nna0.mm"
include "ad2antrr.mm"
include "nnaordi.mm"
include "ancoms.mm"
include "eqeltrrd.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "adantrr.mm"
include "jaod.mm"
include "sylan.mm"
include "syl5.mm"
include "wb.mm"
include "nnmsuc.mm"
include "adantr.mm"
include "sylibrd.mm"
include "exp43.mm"
include "com12.mm"
include "adantld.mm"
include "impd.mm"
include "finds2.mm"
include "vtoclga.mm"
include "com23.mm"
include "exp4a.mm"
include "mpdd.mm"
include "com34.mm"
include "com24.mm"
include "imp31.mm"

theorem nnmordi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( B e. _om /\ C e. _om ) /\ (/) e. C ) -> ( A e. B -> ( C .o A ) e. ( C .o B ) ) )

  proof
    cB
    com
    wcel
    #
    cC
    com
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
    com
    wcel
    #
    @1
    @2
    @6
    wi
    #
    wi
    @3
    @0
    @8
    cA
    cB
    elnn
    expcom
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
    @11
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
    wi
    @11
    @7
    wi
    vx
    cB
    com
    @12
    cB
    wceq
    #
    @16
    @7
    @11
    @17
    @13
    @3
    @15
    @6
    @12
    cB
    cA
    eleq2
    @17
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
    imbi2d
    @16
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
    @22
    comu
    co
    #
    wcel
    #
    wi
    #
    cA
    @22
    csuc
    #
    wcel
    #
    @4
    cC
    @27
    comu
    co
    #
    wcel
    #
    wi
    #
    @11
    vx
    vy
    @12
    c0
    wceq
    #
    @13
    @18
    @15
    @20
    @12
    c0
    cA
    eleq2
    @32
    @14
    @19
    @4
    @12
    c0
    cC
    comu
    oveq2
    eleq2d
    imbi12d
    @12
    @22
    wceq
    #
    @13
    @23
    @15
    @25
    @12
    @22
    cA
    eleq2
    @33
    @14
    @24
    @4
    @12
    @22
    cC
    comu
    oveq2
    eleq2d
    imbi12d
    @12
    @27
    wceq
    #
    @13
    @28
    @15
    @30
    @12
    @27
    cA
    eleq2
    @34
    @14
    @29
    @4
    @12
    @27
    cC
    comu
    oveq2
    eleq2d
    imbi12d
    @21
    @11
    @18
    @20
    cA
    noel
    pm2.21i
    a1i
    @22
    com
    wcel
    #
    @10
    @2
    @26
    @31
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
    @26
    @31
    @1
    @35
    wa
    #
    @2
    @26
    wa
    #
    wa
    #
    @28
    @4
    @24
    cC
    coa
    co
    #
    wcel
    #
    @30
    @28
    @23
    cA
    @22
    wceq
    #
    wo
    #
    @40
    @42
    cA
    @22
    elsuci
    @38
    @24
    com
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
    @22
    nnmcl
    @1
    @35
    simpl
    jca
    @46
    @39
    wa
    @23
    @42
    @43
    @46
    @26
    @23
    @42
    wi
    #
    @2
    @46
    @26
    @47
    @46
    @25
    @42
    @23
    @46
    @24
    @41
    @4
    @24
    cC
    nnaword1
    sseld
    imim2d
    imp
    adantrl
    @46
    @2
    @43
    @42
    wi
    @26
    @46
    @2
    wa
    #
    @42
    @43
    @24
    @41
    wcel
    @48
    @24
    c0
    coa
    co
    #
    @24
    @41
    @45
    @49
    @24
    wceq
    @1
    @2
    @24
    nna0
    ad2antrr
    @46
    @2
    @49
    @41
    wcel
    #
    @1
    @45
    @2
    @50
    wi
    c0
    cC
    @24
    nnaordi
    ancoms
    imp
    eqeltrrd
    @43
    @4
    @24
    @41
    cA
    @22
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
    @30
    @42
    wb
    @39
    @38
    @29
    @41
    @4
    cC
    @22
    nnmsuc
    eleq2d
    adantr
    sylibrd
    exp43
    com12
    adantld
    impd
    finds2
    vtoclga
    com23
    exp4a
    exp4a
    mpdd
    com34
    com24
    imp31
end
