include "cuni.mm"
include "wcel.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "ctopon.mm"
include "ctop.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "lmcl.mm"
include "sylan.mm"
include "cc.mm"
include "cxp.mm"
include "lmfss.mm"
include "rnss.mm"
include "syl.mm"
include "rnxpss.mm"
include "syl6ss.mm"
include "jca.mm"
include "ex.mm"
include "cin.mm"
include "inss2.mm"
include "crest.mm"
include "co.mm"
include "resttopon2.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "sseldi.mm"
include "wb.mm"
include "cv.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "simprl.mm"
include "adantr.mm"
include "elind.mm"
include "2thd.mm"
include "wceq.mm"
include "eleq2i.mm"
include "elrest.mm"
include "biimpa.mm"
include "sylan2b.mm"
include "r19.29r.mm"
include "biantrud.mm"
include "elin.mm"
include "syl6bbr.mm"
include "uztrn2.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "imbi12d.mm"
include "biimpd.mm"
include "eleq2.mm"
include "rexralbidv.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "expdimp.mm"
include "syldan.mm"
include "ralrimdva.mm"
include "simpr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "syl6eleqr.mm"
include "rspcv.mm"
include "sylibrd.mm"
include "impbid.mm"
include "anbi12d.mm"
include "cz.mm"
include "wfn.mm"
include "ffn.mm"
include "simprr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "eqidd.mm"
include "lmbrf.mm"
include "frn.mm"
include "ssind.mm"
include "3bitr4d.mm"
include "pm5.21ndd.mm"

theorem lmss
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cM: class M
  let cV: class V
  let cY: class Y
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  assume lmss.1: |- K = ( J |`t Y )
  assume lmss.2: |- Z = ( ZZ>= ` M )
  assume lmss.3: |- ( ph -> Y e. V )
  assume lmss.4: |- ( ph -> J e. Top )
  assume lmss.5: |- ( ph -> P e. Y )
  assume lmss.6: |- ( ph -> M e. ZZ )
  assume lmss.7: |- ( ph -> F : Z --> Y )


  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> F ( ~~>t ` K ) P ) )

  proof
    wph
    cP
    cJ
    cuni
    #
    wcel
    #
    cF
    crn
    #
    @0
    wss
    #
    wa
    #
    cF
    cP
    cJ
    clm
    cfv
    wbr
    #
    cF
    cP
    cK
    clm
    cfv
    wbr
    #
    wph
    @5
    @4
    wph
    @5
    wa
    #
    @1
    @3
    wph
    cJ
    @0
    ctopon
    cfv
    wcel
    #
    @5
    @1
    wph
    cJ
    ctop
    wcel
    #
    @8
    lmss.4
    cJ
    @0
    @0
    eqid
    toptopon
    #
    sylib
    #
    cP
    cF
    cJ
    @0
    lmcl
    sylan
    @7
    @2
    cc
    @0
    cxp
    #
    crn
    #
    @0
    @7
    cF
    @12
    wss
    #
    @2
    @13
    wss
    wph
    @8
    @5
    @14
    @11
    cP
    cF
    cJ
    @0
    lmfss
    sylan
    cF
    @12
    rnss
    syl
    cc
    @0
    rnxpss
    syl6ss
    jca
    ex
    wph
    @6
    @4
    wph
    @6
    wa
    #
    @1
    @3
    @15
    cY
    @0
    cin
    #
    @0
    cP
    cY
    @0
    inss2
    #
    wph
    cK
    @16
    ctopon
    cfv
    #
    wcel
    #
    @6
    cP
    @16
    wcel
    #
    wph
    cK
    cJ
    cY
    crest
    co
    #
    @18
    lmss.1
    wph
    @8
    cY
    cV
    wcel
    #
    @21
    @18
    wcel
    @11
    lmss.3
    cY
    cJ
    cV
    @0
    resttopon2
    syl2anc
    syl5eqel
    #
    cP
    cF
    cK
    @16
    lmcl
    sylan
    sseldi
    @15
    @2
    @16
    @0
    @15
    @2
    cc
    @16
    cxp
    #
    crn
    #
    @16
    @15
    cF
    @24
    wss
    #
    @2
    @25
    wss
    wph
    @19
    @6
    @26
    @23
    cP
    cF
    cK
    @16
    lmfss
    sylan
    cF
    @24
    rnss
    syl
    cc
    @16
    rnxpss
    syl6ss
    @17
    syl6ss
    jca
    ex
    wph
    @4
    @5
    @6
    wb
    wph
    @4
    wa
    #
    @1
    cP
    vu
    cv
    #
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    @28
    wcel
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
    vj
    cZ
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    wa
    @20
    cP
    vv
    cv
    #
    wcel
    #
    @31
    @39
    wcel
    #
    vk
    @34
    wral
    vj
    cZ
    wrex
    #
    wi
    #
    vv
    cK
    wral
    #
    wa
    @5
    @6
    @27
    @1
    @20
    @38
    @44
    @27
    @1
    @20
    wph
    @1
    @3
    simprl
    #
    @27
    cY
    @0
    cP
    wph
    cP
    cY
    wcel
    #
    @4
    lmss.5
    adantr
    #
    @45
    elind
    2thd
    @27
    @38
    @44
    @27
    @38
    @43
    vv
    cK
    @27
    @39
    cK
    wcel
    #
    @39
    @28
    cY
    cin
    #
    wceq
    #
    vu
    cJ
    wrex
    #
    @38
    @43
    wi
    @48
    @27
    @39
    @21
    wcel
    #
    @51
    cK
    @21
    @39
    lmss.1
    eleq2i
    @27
    @52
    @51
    @27
    @9
    @22
    @52
    @51
    wb
    wph
    @9
    @4
    lmss.4
    adantr
    #
    wph
    @22
    @4
    lmss.3
    adantr
    #
    vu
    @39
    cY
    cJ
    ctop
    cV
    elrest
    syl2anc
    biimpa
    sylan2b
    @27
    @51
    @38
    @43
    @51
    @38
    wa
    @50
    @37
    wa
    #
    vu
    cJ
    wrex
    @27
    @43
    @50
    @37
    vu
    cJ
    r19.29r
    @27
    @55
    @43
    vu
    cJ
    @27
    @28
    cJ
    wcel
    #
    wa
    #
    @50
    @37
    @43
    @57
    @37
    @43
    wi
    @50
    @37
    cP
    @49
    wcel
    #
    @31
    @49
    wcel
    #
    vk
    @34
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    wi
    @57
    @37
    @62
    @27
    @37
    @62
    wb
    @56
    @27
    @29
    @58
    @36
    @61
    @27
    @29
    @29
    @46
    wa
    @58
    @27
    @46
    @29
    @47
    biantrud
    cP
    @28
    cY
    elin
    syl6bbr
    @27
    @35
    @60
    vj
    cZ
    @27
    @33
    cZ
    wcel
    #
    wa
    @32
    @59
    vk
    @34
    @27
    @63
    @30
    @34
    wcel
    #
    @32
    @59
    wb
    #
    @63
    @64
    wa
    @27
    @30
    cZ
    wcel
    #
    @65
    cM
    @30
    @33
    cZ
    lmss.2
    uztrn2
    @27
    @66
    wa
    #
    @32
    @32
    @31
    cY
    wcel
    #
    wa
    @59
    @67
    @68
    @32
    @27
    cZ
    cY
    @30
    cF
    wph
    cZ
    cY
    cF
    wf
    #
    @4
    lmss.7
    adantr
    #
    ffvelrnda
    biantrud
    @31
    @28
    cY
    elin
    syl6bbr
    sylan2
    anassrs
    ralbidva
    rexbidva
    imbi12d
    adantr
    #
    biimpd
    @50
    @43
    @62
    @37
    @50
    @40
    @58
    @42
    @61
    @39
    @49
    cP
    eleq2
    @50
    @41
    @59
    vj
    vk
    cZ
    @34
    @39
    @49
    @31
    eleq2
    rexralbidv
    imbi12d
    #
    imbi2d
    syl5ibrcom
    impd
    rexlimdva
    syl5
    expdimp
    syldan
    ralrimdva
    @27
    @44
    @37
    vu
    cJ
    @57
    @44
    @62
    @37
    @57
    @49
    cK
    wcel
    @44
    @62
    wi
    @57
    @49
    @21
    cK
    @57
    @9
    @22
    @56
    @49
    @21
    wcel
    @27
    @9
    @56
    @53
    adantr
    @27
    @22
    @56
    @54
    adantr
    @27
    @56
    simpr
    @28
    cY
    cJ
    ctop
    cV
    elrestr
    syl3anc
    lmss.1
    syl6eleqr
    @43
    @62
    vv
    @49
    cK
    @72
    rspcv
    syl
    @71
    sylibrd
    ralrimdva
    impbid
    anbi12d
    @27
    vu
    @31
    cP
    vj
    vk
    cF
    cJ
    cM
    @0
    cZ
    @27
    @9
    @8
    @53
    @10
    sylib
    lmss.2
    wph
    cM
    cz
    wcel
    @4
    lmss.6
    adantr
    #
    @27
    cF
    cZ
    wfn
    #
    @3
    cZ
    @0
    cF
    wf
    @27
    @69
    @74
    @70
    cZ
    cY
    cF
    ffn
    syl
    #
    wph
    @1
    @3
    simprr
    #
    cZ
    @0
    cF
    df-f
    sylanbrc
    @67
    @31
    eqidd
    #
    lmbrf
    @27
    vv
    @31
    cP
    vj
    vk
    cF
    cK
    cM
    @16
    cZ
    wph
    @19
    @4
    @23
    adantr
    lmss.2
    @73
    @27
    @74
    @2
    @16
    wss
    cZ
    @16
    cF
    wf
    @75
    @27
    @2
    cY
    @0
    @27
    @69
    @2
    cY
    wss
    @70
    cZ
    cY
    cF
    frn
    syl
    @76
    ssind
    cZ
    @16
    cF
    df-f
    sylanbrc
    @77
    lmbrf
    3bitr4d
    ex
    pm5.21ndd
end
