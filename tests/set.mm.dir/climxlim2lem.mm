include "cr.mm"
include "wcel.mm"
include "clsxlim.mm"
include "wbr.mm"
include "wa.mm"
include "cli.mm"
include "adantr.mm"
include "cz.mm"
include "cxr.mm"
include "wf.mm"
include "simpr.mm"
include "xlimclim2.mm"
include "mpbird.mm"
include "wn.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cuz.mm"
include "wral.mm"
include "wne.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cle.mm"
include "wi.mm"
include "wrex.mm"
include "crp.mm"
include "cc.mm"
include "ffvelrnda.mm"
include "anim1i.mm"
include "adantllr.mm"
include "simplr.mm"
include "eleq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "mpd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "ad4ant14.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cpr.mm"
include "climcl.mm"
include "syl.mm"
include "cfn.mm"
include "prfi.mm"
include "a1i.mm"
include "df-xr.mm"
include "cnrefiisp.mm"
include "reximddv3.mm"
include "clt.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simpll.mm"
include "uztrn2.mm"
include "adantll.mm"
include "rspa.mm"
include "neqne.mm"
include "impel.mm"
include "ad5ant2345.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "adantlr.mm"
include "ad3antrrr.mm"
include "subcld.mm"
include "abscld.mm"
include "adantl3r.mm"
include "rpred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "ad5ant1345.mm"
include "condan.mm"
include "ralrimia.mm"
include "nfcv.mm"
include "climuz.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "rexlimddv2.mm"
include "w3a.mm"
include "uzid3.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "sylan.mm"
include "3adant1.mm"
include "3adant3.mm"
include "eqeltrrd.mm"
include "ad4ant134.mm"
include "xlimconst2.mm"
include "pm2.61dan.mm"

theorem climxlim2lem
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume climxlim2lem.1: |- ( ph -> M e. ZZ )
  assume climxlim2lem.2: |- Z = ( ZZ>= ` M )
  assume climxlim2lem.3: |- ( ph -> F : Z --> RR* )
  assume climxlim2lem.4: |- ( ph -> F : Z --> CC )
  assume climxlim2lem.5: |- ( ph -> F ~~> A )


  assert |- ( ph -> F ~~>* A )

  proof
    wph
    cA
    cr
    wcel
    #
    cF
    cA
    clsxlim
    wbr
    #
    wph
    @0
    wa
    #
    @1
    cF
    cA
    cli
    wbr
    #
    wph
    @3
    @0
    climxlim2lem.5
    adantr
    @2
    cA
    cF
    cM
    cZ
    wph
    cM
    cz
    wcel
    @0
    climxlim2lem.1
    adantr
    climxlim2lem.2
    wph
    cZ
    cxr
    cF
    wf
    #
    @0
    climxlim2lem.3
    adantr
    wph
    @0
    simpr
    xlimclim2
    mpbird
    wph
    @0
    wn
    #
    wa
    #
    vk
    cv
    #
    cF
    cfv
    #
    cA
    wceq
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    @1
    vj
    cZ
    @6
    @8
    cA
    wne
    #
    vx
    cv
    #
    @8
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vk
    cZ
    wral
    #
    @12
    vj
    cZ
    wrex
    #
    vx
    crp
    @6
    vy
    cv
    #
    cc
    wcel
    #
    @21
    cA
    wne
    #
    wa
    #
    @14
    @21
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    cxr
    wral
    #
    @19
    vx
    crp
    wph
    @29
    @19
    @5
    @14
    crp
    wcel
    #
    wph
    @29
    wa
    #
    @18
    vk
    cZ
    @31
    @7
    cZ
    wcel
    #
    wa
    #
    @13
    @17
    @33
    @13
    wa
    @8
    cc
    wcel
    #
    @13
    wa
    #
    @17
    wph
    @32
    @13
    @35
    @29
    wph
    @32
    wa
    @34
    @13
    wph
    cZ
    cc
    @7
    cF
    climxlim2lem.4
    ffvelrnda
    anim1i
    adantllr
    @33
    @35
    @17
    wi
    #
    @13
    @33
    @8
    cxr
    wcel
    @29
    @36
    @31
    cZ
    cxr
    @7
    cF
    wph
    @4
    @29
    climxlim2lem.3
    adantr
    ffvelrnda
    wph
    @29
    @32
    simplr
    @28
    @36
    vy
    @8
    cxr
    @21
    @8
    wceq
    #
    @24
    @35
    @27
    @17
    @37
    @22
    @34
    @23
    @13
    @21
    @8
    cc
    eleq1
    @21
    @8
    cA
    neeq1
    anbi12d
    @37
    @26
    @16
    @14
    cle
    @37
    @25
    @15
    cabs
    @21
    @8
    cA
    cmin
    oveq1
    fveq2d
    breq2d
    imbi12d
    rspcva
    syl2anc
    adantr
    mpd
    ex
    ralrimiva
    ad4ant14
    @6
    vx
    vy
    cA
    cpnf
    cmnf
    cpr
    #
    cxr
    wph
    cA
    cc
    wcel
    #
    @5
    wph
    @3
    @39
    climxlim2lem.5
    cA
    cF
    climcl
    syl
    #
    adantr
    wph
    @5
    simpr
    @38
    cfn
    wcel
    @6
    cpnf
    cmnf
    prfi
    a1i
    df-xr
    cnrefiisp
    reximddv3
    wph
    @30
    @19
    @20
    @5
    wph
    @30
    wa
    #
    @19
    wa
    #
    @16
    @14
    clt
    wbr
    #
    vk
    @11
    wral
    #
    @12
    vj
    cZ
    @42
    @10
    cZ
    wcel
    #
    wa
    #
    @44
    wa
    #
    @9
    vk
    @11
    @46
    @44
    vk
    @42
    @45
    vk
    @41
    @19
    vk
    @41
    vk
    nfv
    @18
    vk
    cZ
    nfra1
    nfan
    @45
    vk
    nfv
    nfan
    @43
    vk
    @11
    nfra1
    nfan
    @47
    @7
    @11
    wcel
    #
    wa
    #
    @9
    @17
    @46
    @48
    @9
    wn
    #
    @17
    @44
    @19
    @45
    @48
    @50
    @17
    @41
    @19
    @45
    wa
    @48
    wa
    #
    @13
    @17
    @50
    @51
    @19
    @32
    @18
    @19
    @45
    @48
    simpll
    @45
    @48
    @32
    @19
    cM
    @7
    @10
    cZ
    climxlim2lem.2
    uztrn2
    #
    adantll
    @18
    vk
    cZ
    rspa
    syl2anc
    @8
    cA
    neqne
    impel
    ad5ant2345
    adantllr
    @49
    @17
    wn
    #
    @50
    @41
    @45
    @44
    @48
    @53
    @19
    @41
    @45
    wa
    #
    @44
    wa
    @48
    wa
    #
    @43
    @53
    @44
    @48
    @43
    @54
    @43
    vk
    @11
    rspa
    adantll
    @55
    @16
    @14
    wph
    @30
    @45
    @44
    @48
    @16
    cr
    wcel
    wph
    @45
    wa
    #
    @44
    wa
    @48
    wa
    #
    @15
    @57
    @8
    cA
    @56
    @48
    @34
    @44
    @56
    @48
    wa
    cZ
    cc
    @7
    cF
    wph
    cZ
    cc
    cF
    wf
    @45
    @48
    climxlim2lem.4
    ad2antrr
    @45
    @48
    @32
    wph
    @52
    adantll
    ffvelrnd
    adantlr
    wph
    @39
    @45
    @44
    @48
    @40
    ad3antrrr
    subcld
    abscld
    adantl3r
    @55
    @14
    @41
    @30
    @45
    @44
    @48
    wph
    @30
    simpr
    ad3antrrr
    rpred
    ltnled
    mpbid
    ad5ant1345
    adantr
    condan
    ralrimia
    @41
    @44
    vj
    cZ
    wrex
    #
    @19
    wph
    @58
    vx
    crp
    wph
    @39
    @58
    vx
    crp
    wral
    #
    wph
    @3
    @39
    @59
    wa
    climxlim2lem.5
    wph
    vx
    cA
    vj
    vk
    cF
    cM
    cZ
    vk
    cF
    nfcv
    #
    climxlim2lem.1
    climxlim2lem.2
    climxlim2lem.4
    climuz
    mpbid
    simprd
    r19.21bi
    adantr
    reximddv3
    adantllr
    rexlimddv2
    @6
    @45
    wa
    #
    @12
    wa
    cA
    vk
    cF
    cM
    @10
    cZ
    @61
    @12
    vk
    @61
    vk
    nfv
    @9
    vk
    @11
    nfra1
    nfan
    @60
    climxlim2lem.2
    wph
    @4
    @5
    @45
    @12
    climxlim2lem.3
    ad3antrrr
    @6
    @45
    @12
    simplr
    wph
    @45
    @12
    cA
    cxr
    wcel
    @5
    wph
    @45
    @12
    w3a
    @10
    cF
    cfv
    #
    cA
    cxr
    @45
    @12
    @62
    cA
    wceq
    #
    wph
    @45
    @10
    @11
    wcel
    @12
    @63
    cM
    @10
    cZ
    climxlim2lem.2
    uzid3
    @9
    @63
    vk
    @10
    @11
    @7
    @10
    wceq
    @8
    @62
    cA
    @7
    @10
    cF
    fveq2
    eqeq1d
    rspcva
    sylan
    3adant1
    wph
    @45
    @62
    cxr
    wcel
    @12
    wph
    cZ
    cxr
    @10
    cF
    climxlim2lem.3
    ffvelrnda
    3adant3
    eqeltrrd
    ad4ant134
    @12
    @48
    @9
    @61
    @9
    vk
    @11
    rspa
    adantll
    xlimconst2
    rexlimddv2
    pm2.61dan
end
