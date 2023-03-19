include "ccic.mm"
include "cfv.mm"
include "wbr.mm"
include "cinito.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "ccat.mm"
include "ciclcl.mm"
include "sylan.mm"
include "cicrcl.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "weu.mm"
include "wral.mm"
include "wi.mm"
include "adantr.mm"
include "cicsym.mm"
include "ciso.mm"
include "wex.mm"
include "eqid.mm"
include "simprr.mm"
include "simprl.mm"
include "cic.mm"
include "isinitoi.mm"
include "mpdan.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "rspcva.mm"
include "nfv.mm"
include "eleq1.mm"
include "cbveu.mm"
include "euex.mm"
include "simpr.mm"
include "ad2antrl.mm"
include "simpl.mm"
include "isohom.mm"
include "sselda.mm"
include "cop.mm"
include "cco.mm"
include "ad2antrr.mm"
include "catcocl.mm"
include "w3a.mm"
include "df-3an.mm"
include "biimpri.mm"
include "ad4antlr.mm"
include "initoeu2lem2.mm"
include "syl113anc.mm"
include "ex.mm"
include "mpand.mm"
include "com23.mm"
include "com15.mm"
include "expd.mm"
include "com24.mm"
include "com12.mm"
include "exlimiv.mm"
include "syl.mm"
include "sylbi.mm"
include "pm2.43i.mm"
include "mpd.mm"
include "adantld.mm"
include "imp.mm"
include "sylbid.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "isinito.mm"
include "mpbird.mm"
include "mp2and.mm"

theorem initoeu2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vg: setvar g
  let vb: setvar b
  let vf: setvar f
  let vh: setvar h
  let vk: setvar k
  assume initoeu1.c: |- ( ph -> C e. Cat )
  assume initoeu1.a: |- ( ph -> A e. ( InitO ` C ) )
  assume initoeu2.i: |- ( ph -> A ( ~=c ` C ) B )


  assert |- ( ph -> B e. ( InitO ` C ) )

  proof
    wph
    cA
    cB
    cC
    ccic
    cfv
    #
    wbr
    #
    cB
    cC
    cinito
    cfv
    #
    wcel
    #
    initoeu2.i
    wph
    @1
    wa
    #
    cA
    cC
    cbs
    cfv
    #
    wcel
    #
    cB
    @5
    wcel
    #
    @3
    wph
    cC
    ccat
    wcel
    #
    @1
    @6
    initoeu1.c
    cC
    cA
    cB
    ciclcl
    sylan
    wph
    @8
    @1
    @7
    initoeu1.c
    cC
    cA
    cB
    cicrcl
    sylan
    @4
    @6
    @7
    wa
    #
    @3
    @4
    @9
    wa
    #
    @3
    vg
    cv
    cB
    vb
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    wcel
    vg
    weu
    #
    vb
    @5
    wral
    @10
    @14
    vb
    @5
    @10
    @11
    @5
    wcel
    #
    @14
    wph
    @9
    @1
    @15
    @14
    wi
    #
    wph
    @9
    wa
    #
    @1
    wa
    cB
    cA
    @0
    wbr
    #
    @16
    @17
    @8
    @1
    @18
    wph
    @8
    @9
    initoeu1.c
    adantr
    #
    cC
    cA
    cB
    cicsym
    sylan
    @17
    @18
    @16
    wi
    @1
    @17
    @18
    vk
    cv
    #
    cB
    cA
    cC
    ciso
    cfv
    #
    co
    #
    wcel
    #
    vk
    wex
    #
    @16
    @17
    @5
    cC
    vk
    @21
    cB
    cA
    @21
    eqid
    #
    @5
    eqid
    #
    @19
    wph
    @6
    @7
    simprr
    wph
    @6
    @7
    simprl
    cic
    @24
    @17
    @16
    @23
    @17
    @16
    wi
    vk
    @17
    @23
    @16
    wph
    @9
    @23
    @16
    wi
    #
    wph
    @6
    vf
    cv
    #
    cA
    va
    cv
    #
    @12
    co
    #
    wcel
    #
    vf
    weu
    #
    va
    @5
    wral
    #
    wa
    #
    @9
    @27
    wi
    #
    wph
    cA
    @2
    wcel
    @34
    initoeu1.a
    wph
    @5
    cC
    vf
    @12
    cA
    va
    @26
    @12
    eqid
    #
    initoeu1.c
    isinitoi
    mpdan
    wph
    @33
    @35
    @6
    @15
    @33
    @9
    @23
    wph
    @14
    @15
    @33
    @9
    @23
    wph
    @14
    wi
    wi
    #
    wi
    #
    @15
    @33
    wa
    @28
    cA
    @11
    @12
    co
    #
    wcel
    #
    vf
    weu
    #
    @38
    @32
    @41
    va
    @11
    @5
    @29
    @11
    wceq
    #
    @31
    @40
    vf
    @42
    @30
    @39
    @28
    @29
    @11
    cA
    @12
    oveq2
    eleq2d
    eubidv
    rspcva
    @15
    @41
    @38
    wi
    @33
    @41
    @15
    @38
    @41
    @15
    @38
    wi
    #
    @41
    vh
    cv
    #
    @39
    wcel
    #
    vh
    weu
    #
    @41
    @43
    wi
    #
    @40
    @45
    vf
    vh
    @40
    vh
    nfv
    @45
    vf
    nfv
    @28
    @44
    @39
    eleq1
    cbveu
    @46
    @45
    vh
    wex
    @47
    @45
    vh
    euex
    @45
    @47
    vh
    @41
    @45
    @43
    @41
    @9
    @15
    @45
    @37
    @41
    @9
    @15
    @45
    @37
    wi
    wph
    @9
    @15
    wa
    #
    @45
    @23
    @41
    @14
    wph
    @48
    @45
    @23
    @41
    @14
    wi
    #
    wi
    wi
    wph
    @48
    wa
    #
    @23
    @45
    @49
    @50
    @23
    @45
    @49
    wi
    @50
    @23
    wa
    #
    @20
    cB
    cA
    @12
    co
    #
    wcel
    #
    @45
    @49
    @50
    @22
    @52
    @20
    @50
    @5
    cC
    @12
    @21
    cB
    cA
    @26
    @36
    @25
    wph
    @8
    @48
    initoeu1.c
    adantr
    #
    @9
    @7
    wph
    @15
    @6
    @7
    simpr
    ad2antrl
    #
    @9
    @6
    wph
    @15
    @6
    @7
    simpl
    ad2antrl
    #
    isohom
    sselda
    @51
    @53
    @45
    wa
    #
    @49
    @51
    @57
    wa
    #
    @44
    @20
    cB
    cA
    cop
    @11
    cC
    cco
    cfv
    #
    co
    co
    @13
    wcel
    #
    @49
    @58
    @5
    cC
    @59
    @20
    @44
    @12
    cB
    cA
    @11
    @26
    @36
    @59
    eqid
    #
    @50
    @8
    @23
    @57
    @54
    ad2antrr
    @50
    @7
    @23
    @57
    @55
    ad2antrr
    @50
    @6
    @23
    @57
    @56
    ad2antrr
    @50
    @15
    @23
    @57
    wph
    @9
    @15
    simprr
    ad2antrr
    @51
    @53
    @45
    simprl
    @51
    @53
    @45
    simprr
    #
    catcocl
    @58
    @60
    wa
    wph
    @6
    @7
    @15
    w3a
    #
    @23
    @45
    @60
    @49
    @58
    wph
    @60
    @50
    wph
    @23
    @57
    wph
    @48
    simpl
    ad2antrr
    adantr
    @48
    @63
    wph
    @23
    @57
    @60
    @63
    @48
    @6
    @7
    @15
    df-3an
    biimpri
    ad4antlr
    @51
    @23
    @57
    @60
    @50
    @23
    simpr
    ad2antrr
    @58
    @45
    @60
    @62
    adantr
    @58
    @60
    simpr
    wph
    cA
    cB
    cC
    @11
    vf
    vg
    @44
    @12
    @21
    @20
    @5
    @59
    initoeu1.c
    initoeu1.a
    @26
    @36
    @25
    @61
    initoeu2lem2
    syl113anc
    mpdan
    ex
    mpand
    ex
    com23
    ex
    com15
    expd
    com24
    com12
    exlimiv
    syl
    sylbi
    pm2.43i
    com12
    adantr
    mpd
    ex
    com15
    adantld
    mpd
    imp
    com12
    exlimiv
    com12
    sylbid
    adantr
    mpd
    an32s
    imp
    ralrimiva
    @10
    @5
    cC
    vg
    @12
    cB
    vb
    @26
    @36
    wph
    @8
    @1
    @9
    initoeu1.c
    ad2antrr
    @4
    @6
    @7
    simprr
    isinito
    mpbird
    ex
    mp2and
    mpdan
end
