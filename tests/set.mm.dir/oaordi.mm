include "con0.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "wi.mm"
include "wa.mm"
include "onelon.mm"
include "adantll.mm"
include "csuc.mm"
include "wss.mm"
include "word.mm"
include "eloni.mm"
include "ordsucss.mm"
include "syl.mm"
include "ad2antlr.mm"
include "sucelon.mm"
include "cv.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "imbi2d.mm"
include "ssid.mm"
include "2a1i.mm"
include "sssucid.mm"
include "sstr2.mm"
include "mpi.mm"
include "oasuc.mm"
include "ancoms.mm"
include "syl5ibr.mm"
include "ex.mm"
include "ad2antrr.mm"
include "a2d.mm"
include "wlim.mm"
include "wral.mm"
include "ciun.mm"
include "sucssel.mm"
include "sylbir.mm"
include "limsuc.mm"
include "biimpd.mm"
include "sylan9r.mm"
include "imp.mm"
include "ssiun2s.mm"
include "adantr.mm"
include "cvv.mm"
include "vex.mm"
include "oalim.mm"
include "mpanr1.mm"
include "adantlr.mm"
include "sseqtr4d.mm"
include "a1d.mm"
include "tfindsg.mm"
include "exp31.mm"
include "syl5bi.mm"
include "com4r.mm"
include "imp31.mm"
include "sseq1d.mm"
include "ovex.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "3syld.mm"
include "an32s.mm"
include "mpdan.mm"

theorem oaordi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( B e. On /\ C e. On ) -> ( A e. B -> ( C +o A ) e. ( C +o B ) ) )

  proof
    cC
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    cB
    wcel
    #
    cC
    cA
    coa
    co
    #
    cC
    cB
    coa
    co
    #
    wcel
    #
    wi
    @0
    @1
    wa
    #
    @2
    @5
    @6
    @2
    wa
    cA
    con0
    wcel
    #
    @5
    @1
    @2
    @7
    @0
    cB
    cA
    onelon
    adantll
    @6
    @7
    @2
    @5
    @6
    @7
    wa
    #
    @2
    @5
    @8
    @2
    cA
    csuc
    #
    cB
    wss
    #
    cC
    @9
    coa
    co
    #
    @4
    wss
    #
    @5
    @1
    @2
    @10
    wi
    #
    @0
    @7
    @1
    cB
    word
    @13
    cB
    eloni
    cA
    cB
    ordsucss
    syl
    ad2antlr
    @0
    @1
    @7
    @10
    @12
    wi
    @1
    @7
    @10
    @0
    @12
    @7
    @9
    con0
    wcel
    #
    @1
    @10
    @0
    @12
    wi
    #
    wi
    cA
    sucelon
    #
    @1
    @14
    @10
    @15
    @0
    @11
    cC
    vx
    cv
    #
    coa
    co
    #
    wss
    #
    wi
    #
    @0
    @11
    @11
    wss
    #
    wi
    @0
    @11
    cC
    vy
    cv
    #
    coa
    co
    #
    wss
    #
    wi
    #
    @0
    @11
    cC
    @22
    csuc
    #
    coa
    co
    #
    wss
    #
    wi
    @15
    vx
    vy
    cB
    @9
    @17
    @9
    wceq
    #
    @19
    @21
    @0
    @29
    @18
    @11
    @11
    @17
    @9
    cC
    coa
    oveq2
    sseq2d
    imbi2d
    @17
    @22
    wceq
    #
    @19
    @24
    @0
    @30
    @18
    @23
    @11
    @17
    @22
    cC
    coa
    oveq2
    sseq2d
    imbi2d
    @17
    @26
    wceq
    #
    @19
    @28
    @0
    @31
    @18
    @27
    @11
    @17
    @26
    cC
    coa
    oveq2
    sseq2d
    imbi2d
    @17
    cB
    wceq
    #
    @19
    @12
    @0
    @32
    @18
    @4
    @11
    @17
    cB
    cC
    coa
    oveq2
    sseq2d
    imbi2d
    @21
    @14
    @0
    @11
    ssid
    2a1i
    @22
    con0
    wcel
    #
    @14
    wa
    @9
    @22
    wss
    #
    wa
    @0
    @24
    @28
    @33
    @0
    @24
    @28
    wi
    #
    wi
    @14
    @34
    @33
    @0
    @35
    @24
    @28
    @33
    @0
    wa
    #
    @11
    @23
    csuc
    #
    wss
    #
    @24
    @23
    @37
    wss
    @38
    @23
    sssucid
    @11
    @23
    @37
    sstr2
    mpi
    @36
    @27
    @37
    @11
    @0
    @33
    @27
    @37
    wceq
    cC
    @22
    oasuc
    ancoms
    sseq2d
    syl5ibr
    ex
    ad2antrr
    a2d
    @17
    wlim
    #
    @14
    wa
    #
    @9
    @17
    wss
    #
    wa
    #
    @20
    @34
    @25
    wi
    vy
    @17
    wral
    @42
    @0
    @19
    @42
    @0
    wa
    @11
    vy
    @17
    @23
    ciun
    #
    @18
    @42
    @11
    @43
    wss
    #
    @0
    @42
    @9
    @17
    wcel
    #
    @44
    @40
    @41
    @45
    @14
    @41
    cA
    @17
    wcel
    #
    @39
    @45
    @14
    @7
    @41
    @46
    wi
    @16
    cA
    @17
    con0
    sucssel
    sylbir
    @39
    @46
    @45
    @17
    cA
    limsuc
    biimpd
    sylan9r
    imp
    vy
    @17
    @23
    @9
    @11
    @22
    @9
    cC
    coa
    oveq2
    ssiun2s
    syl
    adantr
    @40
    @0
    @18
    @43
    wceq
    #
    @41
    @39
    @0
    @47
    @14
    @0
    @39
    @47
    @0
    @17
    cvv
    wcel
    @39
    @47
    vx
    vex
    vy
    cC
    @17
    cvv
    oalim
    mpanr1
    ancoms
    adantlr
    adantlr
    sseqtr4d
    ex
    a1d
    tfindsg
    exp31
    syl5bi
    com4r
    imp31
    @0
    @7
    @12
    @5
    wi
    @1
    @0
    @7
    wa
    #
    @12
    @3
    csuc
    #
    @4
    wss
    #
    @5
    @48
    @11
    @49
    @4
    cC
    cA
    oasuc
    sseq1d
    @3
    cvv
    wcel
    @50
    @5
    wi
    cC
    cA
    coa
    ovex
    @3
    @4
    cvv
    sucssel
    ax-mp
    syl6bi
    adantlr
    3syld
    imp
    an32s
    mpdan
    ex
    ancoms
end
