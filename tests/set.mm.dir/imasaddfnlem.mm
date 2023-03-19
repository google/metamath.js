include "wfun.mm"
include "cdm.mm"
include "cxp.mm"
include "wceq.mm"
include "wfn.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wral.mm"
include "cfv.mm"
include "cop.mm"
include "co.mm"
include "csn.mm"
include "ciun.mm"
include "opex.mm"
include "fvex.mm"
include "relsnop.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "releqd.mm"
include "mpbiri.mm"
include "crn.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wfo.mm"
include "fof.mm"
include "syl.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "sylan.mm"
include "opelxpi.mm"
include "sylancl.mm"
include "snssd.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "dmss.mm"
include "c0.mm"
include "wne.mm"
include "vn0.mm"
include "dmxp.mm"
include "ax-mp.mm"
include "syl6sseq.mm"
include "forn.mm"
include "sqxpeqd.mm"
include "sseqtr4d.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wb.mm"
include "eleq2d.mm"
include "adantr.mm"
include "df-br.mm"
include "eliun.mm"
include "rexbii.mm"
include "bitr2i.mm"
include "3bitr4g.mm"
include "w3a.mm"
include "elsn.mm"
include "vex.mm"
include "opth.mm"
include "syl5bi.mm"
include "eqeq2.mm"
include "biimprd.mm"
include "syl6.mm"
include "impd.mm"
include "3expa.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "alrimiv.mm"
include "mo2icl.mm"
include "ralrimivva.mm"
include "fofn.mm"
include "opeq2.mm"
include "breq1d.mm"
include "mobidv.mm"
include "ralrn.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "opeq1.mm"
include "breq1.mm"
include "ralxp.mm"
include "ssralv.mm"
include "sylc.mm"
include "dffun7.mm"
include "sylanbrc.mm"
include "eqimss2.mm"
include "sylib.mm"
include "snss.mm"
include "opeldm.mm"
include "sylbir.mm"
include "ralimi.mm"
include "sylbi.mm"
include "eleq1d.mm"
include "eleq1.mm"
include "dfss3.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "df-fn.mm"

theorem imasaddfnlem
  let wph: wff ph
  let cB: class B
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cV: class V
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cR: class R
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let vx: setvar x
  let cY: class Y
  assume imasaddf.f: |- ( ph -> F : V -onto-> B )
  assume imasaddf.e: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .x. b ) ) = ( F ` ( p .x. q ) ) ) )
  assume imasaddflem.a: |- ( ph -> .xb = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .x. q ) ) >. } )

  disjoint p q
  disjoint B p
  disjoint B q
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint V a
  disjoint b p
  disjoint b q
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint .x. p
  disjoint .x. q
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint a ph
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint .xb a
  disjoint .xb b
  disjoint .xb p
  disjoint .xb q
  disjoint R p
  disjoint R q
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint p w
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q y
  disjoint q z
  disjoint w y
  disjoint w z
  disjoint V w
  disjoint y z
  disjoint V y
  disjoint V z
  disjoint .x. w
  disjoint X p
  disjoint a x
  disjoint b x
  disjoint p x
  disjoint q x
  disjoint w x
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint ph w
  disjoint .xb w
  disjoint .xb x
  disjoint .xb y
  disjoint .xb z
  disjoint Y p
  disjoint Y q
  assert |- ( ph -> .xb Fn ( B X. B ) )

  proof
    wph
    c.xb
    wfun
    #
    c.xb
    cdm
    #
    cB
    cB
    cxp
    #
    wceq
    c.xb
    @2
    wfn
    wph
    c.xb
    wrel
    #
    vx
    cv
    #
    vw
    cv
    #
    c.xb
    wbr
    #
    vw
    wmo
    #
    vx
    @1
    wral
    #
    @0
    wph
    @3
    vp
    cV
    vq
    cV
    vp
    cv
    #
    cF
    cfv
    #
    vq
    cv
    #
    cF
    cfv
    #
    cop
    #
    @9
    @11
    c.x
    co
    #
    cF
    cfv
    #
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    wrel
    #
    @20
    @18
    wrel
    #
    vp
    cV
    wral
    @21
    vp
    cV
    @21
    @17
    wrel
    #
    vq
    cV
    wral
    @22
    vq
    cV
    @13
    @15
    @10
    @12
    opex
    #
    @14
    cF
    fvex
    #
    relsnop
    rgenw
    vq
    cV
    @17
    reliun
    mpbir
    rgenw
    vp
    cV
    @18
    reliun
    mpbir
    wph
    c.xb
    @19
    imasaddflem.a
    releqd
    mpbiri
    wph
    @1
    cF
    crn
    #
    @25
    cxp
    #
    wss
    @7
    vx
    @26
    wral
    #
    @8
    wph
    @1
    @2
    @26
    wph
    @1
    @2
    cvv
    cxp
    #
    cdm
    #
    @2
    wph
    c.xb
    @28
    wss
    @1
    @29
    wss
    wph
    c.xb
    @19
    @28
    imasaddflem.a
    wph
    @18
    @28
    wss
    #
    vp
    cV
    wral
    @19
    @28
    wss
    wph
    @30
    vp
    cV
    wph
    @9
    cV
    wcel
    #
    wa
    #
    @17
    @28
    wss
    #
    vq
    cV
    wral
    @30
    @32
    @33
    vq
    cV
    wph
    @31
    @11
    cV
    wcel
    #
    @33
    wph
    @31
    @34
    wa
    #
    wa
    #
    @16
    @28
    @36
    @13
    @2
    wcel
    #
    @15
    cvv
    wcel
    @16
    @28
    wcel
    @36
    @10
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    wa
    #
    @37
    wph
    cV
    cB
    cF
    wf
    #
    @35
    @40
    wph
    cV
    cB
    cF
    wfo
    #
    @41
    imasaddf.f
    cV
    cB
    cF
    fof
    syl
    @41
    @31
    @38
    @34
    @39
    cV
    cB
    @9
    cF
    ffvelrn
    cV
    cB
    @11
    cF
    ffvelrn
    anim12dan
    sylan
    @10
    @12
    cB
    cB
    opelxpi
    syl
    @24
    @13
    @15
    @2
    cvv
    opelxpi
    sylancl
    snssd
    anassrs
    ralrimiva
    vq
    cV
    @17
    @28
    iunss
    sylibr
    ralrimiva
    vp
    cV
    @18
    @28
    iunss
    sylibr
    eqsstrd
    c.xb
    @28
    dmss
    syl
    cvv
    c0
    wne
    @29
    @2
    wceq
    vn0
    @2
    cvv
    dmxp
    ax-mp
    syl6sseq
    #
    wph
    @25
    cB
    wph
    @42
    @25
    cB
    wceq
    imasaddf.f
    cV
    cB
    cF
    forn
    syl
    sqxpeqd
    #
    sseqtr4d
    wph
    vy
    cv
    #
    vz
    cv
    #
    cop
    #
    @5
    c.xb
    wbr
    #
    vw
    wmo
    #
    vz
    @25
    wral
    #
    vy
    @25
    wral
    #
    @27
    wph
    @51
    va
    cv
    #
    cF
    cfv
    #
    @46
    cop
    #
    @5
    c.xb
    wbr
    #
    vw
    wmo
    #
    vz
    @25
    wral
    #
    va
    cV
    wral
    #
    wph
    @58
    @53
    vb
    cv
    #
    cF
    cfv
    #
    cop
    #
    @5
    c.xb
    wbr
    #
    vw
    wmo
    #
    vb
    cV
    wral
    #
    va
    cV
    wral
    wph
    @63
    va
    vb
    cV
    cV
    wph
    @52
    cV
    wcel
    @59
    cV
    wcel
    wa
    #
    wa
    #
    @62
    @5
    @52
    @59
    c.x
    co
    cF
    cfv
    #
    wceq
    #
    wi
    #
    vw
    wal
    @63
    @66
    @69
    vw
    @66
    @62
    @61
    @5
    cop
    #
    @17
    wcel
    #
    vq
    cV
    wrex
    #
    vp
    cV
    wrex
    #
    @68
    @66
    @70
    c.xb
    wcel
    #
    @70
    @19
    wcel
    #
    @62
    @73
    wph
    @74
    @75
    wb
    @65
    wph
    c.xb
    @19
    @70
    imasaddflem.a
    eleq2d
    adantr
    @61
    @5
    c.xb
    df-br
    @75
    @70
    @18
    wcel
    #
    vp
    cV
    wrex
    @73
    vp
    @70
    cV
    @18
    eliun
    @76
    @72
    vp
    cV
    vq
    @70
    cV
    @17
    eliun
    rexbii
    bitr2i
    3bitr4g
    @66
    @71
    @68
    vp
    vq
    cV
    cV
    wph
    @65
    @35
    @71
    @68
    wi
    @71
    @70
    @16
    wceq
    #
    wph
    @65
    @35
    w3a
    #
    @68
    @70
    @16
    @61
    @5
    opex
    elsn
    @77
    @61
    @13
    wceq
    #
    @5
    @15
    wceq
    #
    wa
    @78
    @68
    @61
    @5
    @13
    @15
    @53
    @60
    opex
    vw
    vex
    opth
    @78
    @79
    @80
    @68
    @78
    @79
    @67
    @15
    wceq
    #
    @80
    @68
    wi
    @79
    @53
    @10
    wceq
    @60
    @12
    wceq
    wa
    @78
    @81
    @53
    @60
    @10
    @12
    @52
    cF
    fvex
    @59
    cF
    fvex
    opth
    imasaddf.e
    syl5bi
    @81
    @68
    @80
    @67
    @15
    @5
    eqeq2
    biimprd
    syl6
    impd
    syl5bi
    syl5bi
    3expa
    rexlimdvva
    sylbid
    alrimiv
    @62
    vw
    @67
    mo2icl
    syl
    ralrimivva
    wph
    @57
    @64
    va
    cV
    wph
    cF
    cV
    wfn
    #
    @57
    @64
    wb
    wph
    @42
    @82
    imasaddf.f
    cV
    cB
    cF
    fofn
    syl
    #
    @56
    @63
    vz
    vb
    cV
    cF
    @46
    @60
    wceq
    #
    @55
    @62
    vw
    @84
    @54
    @61
    @5
    c.xb
    @46
    @60
    @53
    opeq2
    breq1d
    mobidv
    ralrn
    syl
    ralbidv
    mpbird
    wph
    @82
    @51
    @58
    wb
    @83
    @50
    @57
    vy
    va
    cV
    cF
    @45
    @53
    wceq
    #
    @49
    @56
    vz
    @25
    @85
    @48
    @55
    vw
    @85
    @47
    @54
    @5
    c.xb
    @45
    @53
    @46
    opeq1
    breq1d
    mobidv
    ralbidv
    ralrn
    syl
    mpbird
    @7
    @49
    vx
    vy
    vz
    @25
    @25
    @4
    @47
    wceq
    @6
    @48
    vw
    @4
    @47
    @5
    c.xb
    breq1
    mobidv
    ralxp
    sylibr
    @7
    vx
    @1
    @26
    ssralv
    sylc
    vx
    vw
    c.xb
    dffun7
    sylanbrc
    wph
    @1
    @2
    @43
    wph
    @2
    @26
    @1
    @44
    wph
    @4
    @1
    wcel
    #
    vx
    @26
    wral
    #
    @26
    @1
    wss
    wph
    @47
    @1
    wcel
    #
    vz
    @25
    wral
    #
    vy
    @25
    wral
    #
    @87
    wph
    @90
    @10
    @46
    cop
    #
    @1
    wcel
    #
    vz
    @25
    wral
    #
    vp
    cV
    wral
    #
    wph
    @94
    @13
    @1
    wcel
    #
    vq
    cV
    wral
    #
    vp
    cV
    wral
    #
    wph
    @18
    c.xb
    wss
    #
    vp
    cV
    wral
    #
    @97
    wph
    @19
    c.xb
    wss
    #
    @99
    wph
    c.xb
    @19
    wceq
    @100
    imasaddflem.a
    @19
    c.xb
    eqimss2
    syl
    vp
    cV
    @18
    c.xb
    iunss
    sylib
    @98
    @96
    vp
    cV
    @98
    @17
    c.xb
    wss
    #
    vq
    cV
    wral
    @96
    vq
    cV
    @17
    c.xb
    iunss
    @101
    @95
    vq
    cV
    @101
    @16
    c.xb
    wcel
    @95
    @16
    c.xb
    @13
    @15
    opex
    snss
    @13
    @15
    c.xb
    @23
    @24
    opeldm
    sylbir
    ralimi
    sylbi
    ralimi
    syl
    wph
    @93
    @96
    vp
    cV
    wph
    @82
    @93
    @96
    wb
    @83
    @92
    @95
    vz
    vq
    cV
    cF
    @46
    @12
    wceq
    @91
    @13
    @1
    @46
    @12
    @10
    opeq2
    eleq1d
    ralrn
    syl
    ralbidv
    mpbird
    wph
    @82
    @90
    @94
    wb
    @83
    @89
    @93
    vy
    vp
    cV
    cF
    @45
    @10
    wceq
    #
    @88
    @92
    vz
    @25
    @102
    @47
    @91
    @1
    @45
    @10
    @46
    opeq1
    eleq1d
    ralbidv
    ralrn
    syl
    mpbird
    @86
    @88
    vx
    vy
    vz
    @25
    @25
    @4
    @47
    @1
    eleq1
    ralxp
    sylibr
    vx
    @26
    @1
    dfss3
    sylibr
    eqsstr3d
    eqssd
    c.xb
    @2
    df-fn
    sylanbrc
end
