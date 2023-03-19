include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "comu.mm"
include "co.mm"
include "coa.mm"
include "wceq.mm"
include "csuc.mm"
include "wss.mm"
include "word.mm"
include "wi.mm"
include "simp3l.mm"
include "eloni.mm"
include "ordsucss.mm"
include "3syl.mm"
include "wb.mm"
include "simp2l.mm"
include "suceloni.mm"
include "syl.mm"
include "simp1l.mm"
include "simp1r.mm"
include "on0eln0.mm"
include "mpbird.mm"
include "omword.mm"
include "syl31anc.mm"
include "sylibd.mm"
include "omcl.mm"
include "syl2anc.mm"
include "simp3r.mm"
include "onelon.mm"
include "oaword1.mm"
include "sstr.mm"
include "expcom.mm"
include "syld.mm"
include "simp2r.mm"
include "oaord.mm"
include "biimpa.mm"
include "omsuc.mm"
include "eleqtrrd.mm"
include "ssel.mm"
include "syl6ci.mm"
include "simpr.mm"
include "syl5ib.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "adantr.mm"
include "eleq2d.mm"
include "mpbidi.mm"
include "syl3anc.mm"
include "jaod.mm"

theorem omeulem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( ( ( A e. On /\ A =/= (/) ) /\ ( B e. On /\ C e. A ) /\ ( D e. On /\ E e. A ) ) -> ( ( B e. D \/ ( B = D /\ C e. E ) ) -> ( ( A .o B ) +o C ) e. ( ( A .o D ) +o E ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    c0
    wne
    #
    wa
    #
    cB
    con0
    wcel
    #
    cC
    cA
    wcel
    #
    wa
    #
    cD
    con0
    wcel
    #
    cE
    cA
    wcel
    #
    wa
    #
    w3a
    #
    cB
    cD
    wcel
    #
    cA
    cB
    comu
    co
    #
    cC
    coa
    co
    #
    cA
    cD
    comu
    co
    #
    cE
    coa
    co
    #
    wcel
    #
    cB
    cD
    wceq
    #
    cC
    cE
    wcel
    #
    wa
    #
    @9
    @10
    cA
    cB
    csuc
    #
    comu
    co
    #
    @14
    wss
    #
    @12
    @20
    wcel
    @15
    @9
    @10
    @20
    @13
    wss
    #
    @21
    @9
    @10
    @19
    cD
    wss
    #
    @22
    @9
    @6
    cD
    word
    @10
    @23
    wi
    @2
    @5
    @6
    @7
    simp3l
    #
    cD
    eloni
    cB
    cD
    ordsucss
    3syl
    @9
    @19
    con0
    wcel
    #
    @6
    @0
    c0
    cA
    wcel
    #
    @23
    @22
    wb
    @9
    @3
    @25
    @2
    @3
    @4
    @8
    simp2l
    #
    cB
    suceloni
    syl
    @24
    @0
    @1
    @5
    @8
    simp1l
    #
    @9
    @26
    @1
    @0
    @1
    @5
    @8
    simp1r
    @9
    @0
    @26
    @1
    wb
    @28
    cA
    on0eln0
    syl
    mpbird
    @19
    cD
    cA
    omword
    syl31anc
    sylibd
    @9
    @13
    con0
    wcel
    #
    cE
    con0
    wcel
    #
    @22
    @21
    wi
    #
    @9
    @0
    @6
    @29
    @28
    @24
    cA
    cD
    omcl
    syl2anc
    @9
    @0
    @7
    @30
    @28
    @2
    @5
    @6
    @7
    simp3r
    cA
    cE
    onelon
    syl2anc
    #
    @29
    @30
    wa
    @13
    @14
    wss
    #
    @31
    @13
    cE
    oaword1
    @22
    @33
    @21
    @20
    @13
    @14
    sstr
    expcom
    syl
    syl2anc
    syld
    @9
    @12
    @11
    cA
    coa
    co
    #
    @20
    @9
    cC
    con0
    wcel
    #
    @0
    @11
    con0
    wcel
    #
    @4
    @12
    @34
    wcel
    #
    @9
    @0
    @4
    @35
    @28
    @2
    @3
    @4
    @8
    simp2r
    #
    cA
    cC
    onelon
    syl2anc
    #
    @28
    @9
    @0
    @3
    @36
    @28
    @27
    cA
    cB
    omcl
    syl2anc
    #
    @38
    @35
    @0
    @36
    w3a
    @4
    @37
    cC
    cA
    @11
    oaord
    biimpa
    syl31anc
    @9
    @0
    @3
    @20
    @34
    wceq
    @28
    @27
    cA
    cB
    omsuc
    syl2anc
    eleqtrrd
    @20
    @14
    @12
    ssel
    syl6ci
    @9
    @35
    @30
    @36
    @18
    @15
    wi
    @39
    @32
    @40
    @18
    @12
    @11
    cE
    coa
    co
    #
    wcel
    #
    @15
    @35
    @30
    @36
    w3a
    #
    @18
    @17
    @43
    @42
    @16
    @17
    simpr
    cC
    cE
    @11
    oaord
    syl5ib
    @18
    @41
    @14
    @12
    @16
    @41
    @14
    wceq
    @17
    @16
    @11
    @13
    cE
    coa
    cB
    cD
    cA
    comu
    oveq2
    oveq1d
    adantr
    eleq2d
    mpbidi
    syl3anc
    jaod
end
