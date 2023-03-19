include "crn.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "w3a.mm"
include "wf.mm"
include "frn.mm"
include "syl.mm"
include "wfn.mm"
include "ffn.mm"
include "cz.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "ne0i.mm"
include "wb.mm"
include "breq2.mm"
include "ralrn.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "3jca.mm"
include "adantr.mm"
include "infrecl.mm"
include "simpr.mm"
include "ltaddrpd.mm"
include "rpre.mm"
include "adantl.mm"
include "readdcld.mm"
include "infrglb.mm"
include "mpbid.mm"
include "sselda.mm"
include "adantlr.mm"
include "ad2antlr.mm"
include "ltsub1d.mm"
include "cc.mm"
include "syl3anc.mm"
include "recnd.mm"
include "ad2antrr.mm"
include "pncand.mm"
include "breq2d.mm"
include "bitrd.mm"
include "biimpd.mm"
include "reximdva.mm"
include "mpd.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq1d.mm"
include "rexrn.mm"
include "biimpa.mm"
include "syldan.mm"
include "wi.mm"
include "uztrn2.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simpl.mm"
include "simprr.mm"
include "cfz.mm"
include "fzssuz.mm"
include "uzss.mm"
include "syl6sseqr.mm"
include "eleq2s.mm"
include "ad2antrl.mm"
include "syl5ss.mm"
include "ralrimiva.mm"
include "ssralv.mm"
include "sylc.mm"
include "r19.21bi.mm"
include "c1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "breq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "monoord2.mm"
include "lesub1dd.mm"
include "resubcld.mm"
include "lelttr.mm"
include "mpand.mm"
include "ltsub23.mm"
include "sseldd.mm"
include "infrelb.mm"
include "abssubge0d.mm"
include "3imtr4d.mm"
include "anassrs.mm"
include "ralrimdva.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex.mm"
include "sylancl.mm"
include "eqidd.mm"
include "ffvelrnda.mm"
include "clim2c.mm"

theorem climinf
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vn: setvar n
  let vy: setvar y
  assume climinf.3: |- Z = ( ZZ>= ` M )
  assume climinf.4: |- ( ph -> M e. ZZ )
  assume climinf.5: |- ( ph -> F : Z --> RR )
  assume climinf.6: |- ( ( ph /\ k e. Z ) -> ( F ` ( k + 1 ) ) <_ ( F ` k ) )
  assume climinf.7: |- ( ph -> E. x e. RR A. k e. Z x <_ ( F ` k ) )

  disjoint k ph
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j n
  disjoint j y
  disjoint j ph
  disjoint k n
  disjoint k y
  disjoint n y
  disjoint n ph
  disjoint ph y
  disjoint x y
  disjoint F j
  disjoint F n
  disjoint F y
  disjoint M j
  disjoint Z j
  disjoint Z n
  disjoint Z y
  assert |- ( ph -> F ~~> inf ( ran F , RR , < ) )

  proof
    wph
    cF
    cF
    crn
    #
    cr
    clt
    cinf
    #
    cli
    wbr
    vk
    cv
    #
    cF
    cfv
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
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
    vy
    crp
    wral
    wph
    @11
    vy
    crp
    wph
    @6
    crp
    wcel
    #
    wa
    #
    @8
    cF
    cfv
    #
    @6
    cmin
    co
    #
    @1
    clt
    wbr
    #
    vj
    cZ
    wrex
    #
    @11
    wph
    @12
    @2
    @6
    cmin
    co
    #
    @1
    clt
    wbr
    #
    vk
    @0
    wrex
    #
    @17
    @13
    @2
    @1
    @6
    caddc
    co
    #
    clt
    wbr
    #
    vk
    @0
    wrex
    #
    @20
    @13
    @1
    @21
    clt
    wbr
    #
    @23
    @13
    @1
    @6
    @13
    @0
    cr
    wss
    #
    @0
    c0
    wne
    #
    vx
    cv
    #
    @6
    cle
    wbr
    #
    vy
    @0
    wral
    #
    vx
    cr
    wrex
    #
    w3a
    #
    @1
    cr
    wcel
    #
    wph
    @31
    @12
    wph
    @25
    @26
    @30
    wph
    cZ
    cr
    cF
    wf
    #
    @25
    climinf.5
    cZ
    cr
    cF
    frn
    syl
    #
    wph
    cM
    cF
    cfv
    #
    @0
    wcel
    #
    @26
    wph
    cF
    cZ
    wfn
    #
    cM
    cZ
    wcel
    @36
    wph
    @33
    @37
    climinf.5
    cZ
    cr
    cF
    ffn
    syl
    #
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    cM
    @39
    wcel
    climinf.4
    cM
    uzid
    syl
    climinf.3
    syl6eleqr
    cZ
    cM
    cF
    fnfvelrn
    syl2anc
    @0
    @35
    ne0i
    syl
    #
    wph
    @30
    @27
    @3
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    climinf.7
    wph
    @37
    @30
    @43
    wb
    @38
    @37
    @29
    @42
    vx
    cr
    @28
    @41
    vy
    vk
    cZ
    cF
    @6
    @3
    @27
    cle
    breq2
    ralrn
    rexbidv
    syl
    mpbird
    #
    3jca
    adantr
    #
    vx
    vy
    @0
    infrecl
    #
    syl
    #
    wph
    @12
    simpr
    ltaddrpd
    @13
    @31
    @21
    cr
    wcel
    @24
    @23
    wb
    @45
    @13
    @1
    @6
    @47
    @12
    @6
    cr
    wcel
    #
    wph
    @6
    rpre
    #
    adantl
    readdcld
    vx
    vy
    vk
    @0
    @21
    infrglb
    syl2anc
    mpbid
    @13
    @22
    @19
    vk
    @0
    @13
    @2
    @0
    wcel
    #
    wa
    #
    @22
    @19
    @51
    @22
    @18
    @21
    @6
    cmin
    co
    #
    clt
    wbr
    @19
    @51
    @2
    @21
    @6
    wph
    @50
    @2
    cr
    wcel
    @12
    wph
    @0
    cr
    @2
    @34
    sselda
    adantlr
    @51
    @1
    @6
    @13
    @32
    @50
    @47
    adantr
    @12
    @48
    wph
    @50
    @49
    ad2antlr
    #
    readdcld
    @53
    ltsub1d
    @51
    @52
    @1
    @18
    clt
    @51
    @1
    @6
    wph
    @1
    cc
    wcel
    @12
    @50
    wph
    @1
    wph
    @25
    @26
    @30
    @32
    @34
    @40
    @44
    @46
    syl3anc
    #
    recnd
    #
    ad2antrr
    @51
    @6
    @53
    recnd
    pncand
    breq2d
    bitrd
    biimpd
    reximdva
    mpd
    wph
    @20
    @17
    wph
    @37
    @20
    @17
    wb
    @38
    @19
    @16
    vk
    vj
    cZ
    cF
    @2
    @14
    wceq
    @18
    @15
    @1
    clt
    @2
    @14
    @6
    cmin
    oveq1
    breq1d
    rexrn
    syl
    biimpa
    syldan
    @13
    @16
    @10
    vj
    cZ
    @13
    @8
    cZ
    wcel
    #
    wa
    @16
    @7
    vk
    @9
    @13
    @56
    @2
    @9
    wcel
    #
    @16
    @7
    wi
    @13
    @56
    @57
    wa
    #
    wa
    #
    @14
    @1
    cmin
    co
    #
    @6
    clt
    wbr
    #
    @4
    @6
    clt
    wbr
    #
    @16
    @7
    @59
    @4
    @60
    cle
    wbr
    #
    @61
    @62
    @59
    @3
    @14
    @1
    @13
    @33
    @2
    cZ
    wcel
    #
    @3
    cr
    wcel
    @58
    wph
    @33
    @12
    climinf.5
    adantr
    #
    cM
    @2
    @8
    cZ
    climinf.3
    uztrn2
    #
    cZ
    cr
    @2
    cF
    ffvelrn
    syl2an
    #
    @13
    @33
    @56
    @14
    cr
    wcel
    #
    @58
    @65
    @56
    @57
    simpl
    cZ
    cr
    @8
    cF
    ffvelrn
    syl2an
    #
    wph
    @32
    @12
    @58
    @54
    ad2antrr
    #
    @59
    vn
    cF
    @8
    @2
    @13
    @56
    @57
    simprr
    @59
    vn
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    vn
    @8
    @2
    cfz
    co
    #
    @59
    @74
    cZ
    wss
    @73
    vn
    cZ
    wral
    #
    @73
    vn
    @74
    wral
    @59
    @74
    @9
    cZ
    @8
    @2
    fzssuz
    @56
    @9
    cZ
    wss
    #
    @13
    @57
    @76
    @8
    @39
    cZ
    @8
    @39
    wcel
    @9
    @39
    cZ
    cM
    @8
    uzss
    climinf.3
    syl6sseqr
    climinf.3
    eleq2s
    ad2antrl
    #
    syl5ss
    wph
    @75
    @12
    @58
    wph
    @33
    @75
    climinf.5
    @33
    @73
    vn
    cZ
    cZ
    cr
    @71
    cF
    ffvelrn
    ralrimiva
    syl
    ad2antrr
    @73
    vn
    @74
    cZ
    ssralv
    sylc
    r19.21bi
    @59
    @71
    @8
    @2
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    @71
    cZ
    wcel
    #
    @71
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @72
    cle
    wbr
    #
    @59
    @79
    cZ
    @71
    @59
    @79
    @9
    cZ
    @8
    @78
    fzssuz
    @77
    syl5ss
    sselda
    @59
    @2
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @3
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    @80
    @83
    wph
    @87
    @12
    @58
    wph
    @86
    vk
    cZ
    climinf.6
    ralrimiva
    ad2antrr
    @86
    @83
    vk
    @71
    cZ
    @2
    @71
    wceq
    #
    @85
    @82
    @3
    @72
    cle
    @88
    @84
    @81
    cF
    @2
    @71
    c1
    caddc
    oveq1
    fveq2d
    @2
    @71
    cF
    fveq2
    breq12d
    rspccva
    sylan
    syldan
    monoord2
    lesub1dd
    @59
    @4
    cr
    wcel
    @60
    cr
    wcel
    @48
    @63
    @61
    wa
    @62
    wi
    @59
    @3
    @1
    @67
    @70
    resubcld
    @59
    @14
    @1
    @69
    @70
    resubcld
    @12
    @48
    wph
    @58
    @49
    ad2antlr
    #
    @4
    @60
    @6
    lelttr
    syl3anc
    mpand
    @59
    @68
    @48
    @32
    @16
    @61
    wb
    @69
    @89
    @70
    @14
    @6
    @1
    ltsub23
    syl3anc
    @59
    @5
    @4
    @6
    clt
    @59
    @1
    @3
    @70
    @59
    @0
    cr
    @3
    wph
    @25
    @12
    @58
    @34
    ad2antrr
    #
    @13
    @37
    @64
    @3
    @0
    wcel
    #
    @58
    wph
    @37
    @12
    @38
    adantr
    @66
    cZ
    @2
    cF
    fnfvelrn
    syl2an
    #
    sseldd
    @59
    @25
    @30
    @91
    @1
    @3
    cle
    wbr
    @90
    wph
    @30
    @12
    @58
    @44
    ad2antrr
    @92
    vx
    vy
    @3
    @0
    infrelb
    syl3anc
    abssubge0d
    breq1d
    3imtr4d
    anassrs
    ralrimdva
    reximdva
    mpd
    ralrimiva
    wph
    vy
    @1
    @3
    vj
    vk
    cF
    cM
    cvv
    cZ
    climinf.3
    climinf.4
    wph
    @33
    cZ
    cvv
    wcel
    cF
    cvv
    wcel
    climinf.5
    cZ
    @39
    cvv
    climinf.3
    cM
    cuz
    fvex
    eqeltri
    cZ
    cr
    cvv
    cF
    fex
    sylancl
    wph
    @64
    wa
    #
    @3
    eqidd
    @55
    @93
    @3
    wph
    cZ
    cr
    @2
    cF
    climinf.5
    ffvelrnda
    recnd
    clim2c
    mpbird
end
