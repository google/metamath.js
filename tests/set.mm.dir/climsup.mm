include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
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
include "breq1.mm"
include "ralrn.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "3jca.mm"
include "suprcl.mm"
include "ltsubrp.mm"
include "sylan.mm"
include "adantr.mm"
include "rpre.mm"
include "resubcl.mm"
include "syl2an.mm"
include "suprlub.mm"
include "mpbid.mm"
include "breq2.mm"
include "rexrn.mm"
include "biimpa.mm"
include "syldan.mm"
include "wi.mm"
include "ffvelrn.mm"
include "ad2ant2r.mm"
include "uztrn2.mm"
include "ad2antrr.mm"
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
include "caddc.mm"
include "sselda.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspccva.mm"
include "monoord.mm"
include "lesub2dd.mm"
include "resubcld.mm"
include "ad2antlr.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "ltsub23.mm"
include "suprub.mm"
include "abssuble0d.mm"
include "breq1d.mm"
include "3imtr4d.mm"
include "anassrs.mm"
include "ralrimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex.mm"
include "sylancl.mm"
include "eqidd.mm"
include "recnd.mm"
include "clim2c.mm"

theorem climsup
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vn: setvar n
  let vy: setvar y
  assume climsup.1: |- Z = ( ZZ>= ` M )
  assume climsup.2: |- ( ph -> M e. ZZ )
  assume climsup.3: |- ( ph -> F : Z --> RR )
  assume climsup.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) <_ ( F ` ( k + 1 ) ) )
  assume climsup.5: |- ( ph -> E. x e. RR A. k e. Z ( F ` k ) <_ x )

  disjoint k x
  disjoint F k
  disjoint F x
  disjoint k ph
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k n
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F y
  disjoint M j
  disjoint j ph
  disjoint n ph
  disjoint ph y
  disjoint Z j
  disjoint Z n
  disjoint Z y
  assert |- ( ph -> F ~~> sup ( ran F , RR , < ) )

  proof
    wph
    cF
    cF
    crn
    #
    cr
    clt
    csup
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
    @10
    vy
    crp
    wph
    @5
    crp
    wcel
    #
    wa
    #
    @1
    @5
    cmin
    co
    #
    @7
    cF
    cfv
    #
    clt
    wbr
    #
    vj
    cZ
    wrex
    #
    @10
    wph
    @11
    @13
    @2
    clt
    wbr
    #
    vk
    @0
    wrex
    #
    @16
    @12
    @13
    @1
    clt
    wbr
    #
    @18
    wph
    @1
    cr
    wcel
    #
    @11
    @19
    wph
    @0
    cr
    wss
    #
    @0
    c0
    wne
    #
    @5
    vx
    cv
    #
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
    @20
    wph
    @21
    @22
    @26
    wph
    cZ
    cr
    cF
    wf
    #
    @21
    climsup.3
    cZ
    cr
    cF
    frn
    syl
    wph
    cM
    cF
    cfv
    #
    @0
    wcel
    #
    @22
    wph
    cF
    cZ
    wfn
    #
    cM
    cZ
    wcel
    @30
    wph
    @28
    @31
    climsup.3
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
    @33
    wcel
    climsup.2
    cM
    uzid
    syl
    climsup.1
    syl6eleqr
    cZ
    cM
    cF
    fnfvelrn
    syl2anc
    @0
    @29
    ne0i
    syl
    wph
    @26
    @3
    @23
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
    climsup.5
    wph
    @31
    @26
    @36
    wb
    @32
    @31
    @25
    @35
    vx
    cr
    @24
    @34
    vy
    vk
    cZ
    cF
    @5
    @3
    @23
    cle
    breq1
    ralrn
    rexbidv
    syl
    mpbird
    3jca
    #
    vx
    vy
    @0
    suprcl
    syl
    #
    @1
    @5
    ltsubrp
    sylan
    @12
    @27
    @13
    cr
    wcel
    #
    @19
    @18
    wb
    wph
    @27
    @11
    @37
    adantr
    wph
    @20
    @5
    cr
    wcel
    #
    @39
    @11
    @38
    @5
    rpre
    #
    @1
    @5
    resubcl
    syl2an
    vx
    vy
    vk
    @0
    @13
    suprlub
    syl2anc
    mpbid
    wph
    @18
    @16
    wph
    @31
    @18
    @16
    wb
    @32
    @17
    @15
    vk
    vj
    cZ
    cF
    @2
    @14
    @13
    clt
    breq2
    rexrn
    syl
    biimpa
    syldan
    @12
    @15
    @9
    vj
    cZ
    @12
    @7
    cZ
    wcel
    #
    wa
    @15
    @6
    vk
    @8
    @12
    @42
    @2
    @8
    wcel
    #
    @15
    @6
    wi
    @12
    @42
    @43
    wa
    #
    wa
    #
    @1
    @14
    cmin
    co
    #
    @5
    clt
    wbr
    #
    @1
    @3
    cmin
    co
    #
    @5
    clt
    wbr
    #
    @15
    @6
    @45
    @48
    @46
    cle
    wbr
    #
    @47
    @49
    @45
    @14
    @3
    @1
    wph
    @42
    @14
    cr
    wcel
    #
    @11
    @43
    wph
    @28
    @42
    @51
    climsup.3
    cZ
    cr
    @7
    cF
    ffvelrn
    sylan
    ad2ant2r
    #
    @12
    @28
    @2
    cZ
    wcel
    #
    @3
    cr
    wcel
    #
    @44
    wph
    @28
    @11
    climsup.3
    adantr
    cM
    @2
    @7
    cZ
    climsup.1
    uztrn2
    #
    cZ
    cr
    @2
    cF
    ffvelrn
    #
    syl2an
    #
    wph
    @20
    @11
    @44
    @38
    ad2antrr
    #
    @45
    vn
    cF
    @7
    @2
    @12
    @42
    @43
    simprr
    @45
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
    @7
    @2
    cfz
    co
    #
    @45
    @62
    cZ
    wss
    @61
    vn
    cZ
    wral
    #
    @61
    vn
    @62
    wral
    @45
    @62
    @8
    cZ
    @7
    @2
    fzssuz
    @42
    @8
    cZ
    wss
    #
    @12
    @43
    @64
    @7
    @33
    cZ
    @7
    @33
    wcel
    @8
    @33
    cZ
    cM
    @7
    uzss
    climsup.1
    syl6sseqr
    climsup.1
    eleq2s
    ad2antrl
    #
    syl5ss
    wph
    @63
    @11
    @44
    wph
    @28
    @63
    climsup.3
    @28
    @61
    vn
    cZ
    cZ
    cr
    @59
    cF
    ffvelrn
    ralrimiva
    syl
    ad2antrr
    @61
    vn
    @62
    cZ
    ssralv
    sylc
    r19.21bi
    @45
    @59
    @7
    @2
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    @59
    cZ
    wcel
    #
    @60
    @59
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cle
    wbr
    #
    @45
    @67
    cZ
    @59
    @45
    @67
    @8
    cZ
    @7
    @66
    fzssuz
    @65
    syl5ss
    sselda
    @45
    @3
    @2
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    @68
    @71
    wph
    @75
    @11
    @44
    wph
    @74
    vk
    cZ
    climsup.4
    ralrimiva
    ad2antrr
    @74
    @71
    vk
    @59
    cZ
    vk
    vn
    weq
    #
    @3
    @60
    @73
    @70
    cle
    @2
    @59
    cF
    fveq2
    @76
    @72
    @69
    cF
    @2
    @59
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspccva
    sylan
    syldan
    monoord
    lesub2dd
    @45
    @48
    cr
    wcel
    @46
    cr
    wcel
    @40
    @50
    @47
    wa
    @49
    wi
    @45
    @1
    @3
    @58
    @57
    resubcld
    @45
    @1
    @14
    @58
    @52
    resubcld
    @11
    @40
    wph
    @44
    @41
    ad2antlr
    #
    @48
    @46
    @5
    lelttr
    syl3anc
    mpand
    @45
    @20
    @40
    @51
    @15
    @47
    wb
    @58
    @77
    @52
    @1
    @5
    @14
    ltsub23
    syl3anc
    @45
    @4
    @48
    @5
    clt
    @45
    @3
    @1
    @57
    @58
    @45
    @27
    @3
    @0
    wcel
    #
    @3
    @1
    cle
    wbr
    wph
    @27
    @11
    @44
    @37
    ad2antrr
    @12
    @31
    @53
    @78
    @44
    wph
    @31
    @11
    @32
    adantr
    @55
    cZ
    @2
    cF
    fnfvelrn
    syl2an
    vx
    vy
    @0
    @3
    suprub
    syl2anc
    abssuble0d
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
    climsup.1
    climsup.2
    wph
    @28
    cZ
    cvv
    wcel
    cF
    cvv
    wcel
    climsup.3
    cZ
    @33
    cvv
    climsup.1
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
    @53
    wa
    #
    @3
    eqidd
    wph
    @1
    @38
    recnd
    @79
    @3
    wph
    @28
    @53
    @54
    climsup.3
    @56
    sylan
    recnd
    clim2c
    mpbird
end
