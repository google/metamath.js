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
include "csn.mm"
include "co.mm"
include "cmpt2.mm"
include "ciun.mm"
include "eqid.mm"
include "fvex.mm"
include "fnmpt2i.mm"
include "fnrel.mm"
include "ax-mp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "imasvsca.mm"
include "releqd.mm"
include "mpbiri.mm"
include "crn.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "dffn2.mm"
include "mpbi.mm"
include "fssxp.mm"
include "wfo.mm"
include "fof.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "snssd.mm"
include "xpss2.mm"
include "xpss1.mm"
include "3syl.mm"
include "syl5ss.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "dmss.mm"
include "c0.mm"
include "wne.mm"
include "vn0.mm"
include "dmxp.mm"
include "syl6sseq.mm"
include "forn.mm"
include "xpeq2d.mm"
include "sseqtr4d.mm"
include "cop.mm"
include "wi.mm"
include "wal.mm"
include "df-br.mm"
include "wb.mm"
include "eleq2d.mm"
include "adantr.mm"
include "wrex.mm"
include "eliun.mm"
include "w3a.mm"
include "df-3an.mm"
include "mpt2fun.mm"
include "funopfv.mm"
include "df-ov.mm"
include "opex.mm"
include "vex.mm"
include "opeldm.mm"
include "dmmpt2.mm"
include "syl6eleq.mm"
include "opelxp.mm"
include "sylib.mm"
include "weq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqidd.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "cbvmpt2v.mm"
include "ovmpt2.mm"
include "syl5eqr.mm"
include "eqtr3d.mm"
include "adantl.mm"
include "simprd.mm"
include "elsni.mm"
include "imp.mm"
include "sylan2.mm"
include "eqtr4d.mm"
include "ex.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
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
include "breq1.mm"
include "ralxp.mm"
include "ssralv.mm"
include "sylc.mm"
include "dffun7.mm"
include "sylanbrc.mm"
include "eqimss2.mm"
include "r19.21bi.mm"
include "adantrl.mm"
include "syl5eqssr.mm"
include "simprl.mm"
include "snid.mm"
include "opelxpi.mm"
include "sylancl.mm"
include "sseldd.mm"
include "eleq1d.mm"
include "eleq1.mm"
include "dfss3.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "df-fn.mm"

theorem imasvscafn
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let cY: class Y
  assume imasvscaf.u: |- ( ph -> U = ( F "s R ) )
  assume imasvscaf.v: |- ( ph -> V = ( Base ` R ) )
  assume imasvscaf.f: |- ( ph -> F : V -onto-> B )
  assume imasvscaf.r: |- ( ph -> R e. Z )
  assume imasvscaf.g: |- G = ( Scalar ` R )
  assume imasvscaf.k: |- K = ( Base ` G )
  assume imasvscaf.q: |- .x. = ( .s ` R )
  assume imasvscaf.s: |- .xb = ( .s ` U )
  assume imasvscaf.e: |- ( ( ph /\ ( p e. K /\ a e. V /\ q e. V ) ) -> ( ( F ` a ) = ( F ` q ) -> ( F ` ( p .x. a ) ) = ( F ` ( p .x. q ) ) ) )

  disjoint a p
  disjoint a q
  disjoint F a
  disjoint p q
  disjoint F p
  disjoint F q
  disjoint K a
  disjoint K p
  disjoint K q
  disjoint a ph
  disjoint p ph
  disjoint ph q
  disjoint B p
  disjoint B q
  disjoint R p
  disjoint R q
  disjoint .x. p
  disjoint .x. q
  disjoint .xb a
  disjoint .xb p
  disjoint .xb q
  disjoint V a
  disjoint V p
  disjoint V q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint ph w
  disjoint ph x
  disjoint U x
  disjoint B x
  disjoint R x
  disjoint .x. w
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .xb w
  disjoint .xb x
  disjoint .xb y
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint X p
  disjoint X x
  disjoint Y p
  disjoint Y q
  disjoint Y x
  assert |- ( ph -> .xb Fn ( K X. B ) )

  proof
    wph
    c.xb
    wfun
    #
    c.xb
    cdm
    #
    cK
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
    vq
    cV
    vp
    vx
    cK
    vq
    cv
    #
    cF
    cfv
    #
    csn
    #
    vp
    cv
    #
    @9
    c.x
    co
    #
    cF
    cfv
    #
    cmpt2
    #
    ciun
    #
    wrel
    #
    @17
    @15
    wrel
    #
    vq
    cV
    wral
    @18
    vq
    cV
    @15
    cK
    @11
    cxp
    #
    wfn
    #
    @18
    vp
    vx
    cK
    @11
    @14
    @15
    @15
    eqid
    #
    @13
    cF
    fvex
    #
    fnmpt2i
    #
    @19
    @15
    fnrel
    ax-mp
    rgenw
    vq
    cV
    @15
    reliun
    mpbir
    wph
    c.xb
    @16
    wph
    vx
    cB
    cR
    c.xb
    c.x
    cU
    cF
    cG
    cK
    cV
    cZ
    vq
    vp
    imasvscaf.u
    imasvscaf.v
    imasvscaf.f
    imasvscaf.r
    imasvscaf.g
    imasvscaf.k
    imasvscaf.q
    imasvscaf.s
    imasvsca
    #
    releqd
    mpbiri
    wph
    @1
    cK
    cF
    crn
    #
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
    @16
    @28
    @24
    wph
    @15
    @28
    wss
    #
    vq
    cV
    wral
    @16
    @28
    wss
    wph
    @30
    vq
    cV
    wph
    @9
    cV
    wcel
    #
    wa
    #
    @15
    @19
    cvv
    cxp
    #
    @28
    @19
    cvv
    @15
    wf
    #
    @15
    @33
    wss
    @20
    @34
    @23
    @19
    @15
    dffn2
    mpbi
    @19
    cvv
    @15
    fssxp
    ax-mp
    @32
    @11
    cB
    wss
    @19
    @2
    wss
    @33
    @28
    wss
    @32
    @10
    cB
    wph
    cV
    cB
    @9
    cF
    wph
    cV
    cB
    cF
    wfo
    #
    cV
    cB
    cF
    wf
    imasvscaf.f
    cV
    cB
    cF
    fof
    syl
    ffvelrnda
    snssd
    @11
    cB
    cK
    xpss2
    @19
    @2
    cvv
    xpss1
    3syl
    syl5ss
    ralrimiva
    vq
    cV
    @15
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
    cK
    wph
    @35
    @25
    cB
    wceq
    imasvscaf.f
    cV
    cB
    cF
    forn
    syl
    xpeq2d
    #
    sseqtr4d
    wph
    @12
    vy
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
    vy
    @25
    wral
    #
    vp
    cK
    wral
    #
    @27
    wph
    @43
    @12
    va
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
    va
    cV
    wral
    #
    vp
    cK
    wral
    wph
    @48
    vp
    va
    cK
    cV
    wph
    @12
    cK
    wcel
    #
    @44
    cV
    wcel
    #
    wa
    #
    wa
    #
    @47
    @5
    @12
    @44
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
    @48
    @53
    @56
    vw
    @47
    @46
    @5
    cop
    #
    c.xb
    wcel
    #
    @53
    @55
    @46
    @5
    c.xb
    df-br
    @53
    @58
    @57
    @16
    wcel
    #
    @55
    wph
    @58
    @59
    wb
    @52
    wph
    c.xb
    @16
    @57
    @24
    eleq2d
    adantr
    @59
    @57
    @15
    wcel
    #
    vq
    cV
    wrex
    @53
    @55
    vq
    @57
    cV
    @15
    eliun
    @53
    @60
    @55
    vq
    cV
    wph
    @52
    @31
    @60
    @55
    wi
    #
    @52
    @31
    wa
    wph
    @50
    @51
    @31
    w3a
    #
    @61
    @50
    @51
    @31
    df-3an
    wph
    @62
    wa
    #
    @60
    @55
    @63
    @60
    wa
    @5
    @14
    @54
    @60
    @5
    @14
    wceq
    @63
    @60
    @46
    @15
    cfv
    #
    @5
    @14
    @15
    wfun
    @60
    @64
    @5
    wceq
    wi
    vp
    vx
    cK
    @11
    @14
    @15
    @21
    mpt2fun
    @46
    @5
    @15
    funopfv
    ax-mp
    @60
    @64
    @12
    @45
    @15
    co
    #
    @14
    @12
    @45
    @15
    df-ov
    @60
    @50
    @45
    @11
    wcel
    #
    wa
    #
    @65
    @14
    wceq
    @60
    @46
    @19
    wcel
    @67
    @60
    @46
    @15
    cdm
    #
    @19
    @46
    @5
    @15
    @12
    @45
    opex
    vw
    vex
    opeldm
    vp
    vx
    cK
    @11
    @14
    @15
    @21
    @22
    dmmpt2
    #
    syl6eleq
    @12
    @45
    cK
    @11
    opelxp
    sylib
    #
    vz
    vy
    @12
    @45
    cK
    @11
    vz
    cv
    #
    @9
    c.x
    co
    #
    cF
    cfv
    #
    @14
    @15
    @14
    vz
    vp
    weq
    @72
    @13
    cF
    @71
    @12
    @9
    c.x
    oveq1
    fveq2d
    #
    @38
    @45
    wceq
    #
    @14
    eqidd
    vp
    vx
    vz
    vy
    cK
    @11
    @14
    @73
    @73
    vp
    vz
    weq
    @73
    @14
    @73
    @14
    wceq
    vz
    vp
    @74
    equcoms
    eqcomd
    vx
    vy
    weq
    @73
    eqidd
    cbvmpt2v
    @22
    ovmpt2
    syl
    syl5eqr
    eqtr3d
    adantl
    @60
    @63
    @45
    @10
    wceq
    #
    @54
    @14
    wceq
    #
    @60
    @66
    @76
    @60
    @50
    @66
    @70
    simprd
    @45
    @10
    elsni
    syl
    @63
    @76
    @77
    imasvscaf.e
    imp
    sylan2
    eqtr4d
    ex
    sylan2br
    anassrs
    rexlimdva
    syl5bi
    sylbid
    syl5bi
    alrimiv
    @47
    vw
    @54
    mo2icl
    syl
    ralrimivva
    wph
    @42
    @49
    vp
    cK
    wph
    @35
    cF
    cV
    wfn
    #
    @42
    @49
    wb
    imasvscaf.f
    cV
    cB
    cF
    fofn
    #
    @41
    @48
    vy
    va
    cV
    cF
    @75
    @40
    @47
    vw
    @75
    @39
    @46
    @5
    c.xb
    @38
    @45
    @12
    opeq2
    breq1d
    mobidv
    ralrn
    3syl
    ralbidv
    mpbird
    @7
    @41
    vx
    vp
    vy
    cK
    @25
    @4
    @39
    wceq
    @6
    @40
    vw
    @4
    @39
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
    @36
    wph
    @2
    @26
    @1
    @37
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
    @39
    @1
    wcel
    #
    vy
    @25
    wral
    #
    vp
    cK
    wral
    #
    @81
    wph
    @84
    @12
    @10
    cop
    #
    @1
    wcel
    #
    vq
    cV
    wral
    #
    vp
    cK
    wral
    wph
    @86
    vp
    vq
    cK
    cV
    wph
    @50
    @31
    wa
    wa
    #
    @19
    @1
    @85
    @88
    @19
    @68
    @1
    @69
    @88
    @15
    c.xb
    wss
    #
    @68
    @1
    wss
    wph
    @31
    @89
    @50
    wph
    @89
    vq
    cV
    wph
    @16
    c.xb
    wss
    #
    @89
    vq
    cV
    wral
    wph
    c.xb
    @16
    wceq
    @90
    @24
    @16
    c.xb
    eqimss2
    syl
    vq
    cV
    @15
    c.xb
    iunss
    sylib
    r19.21bi
    adantrl
    @15
    c.xb
    dmss
    syl
    syl5eqssr
    @88
    @50
    @10
    @11
    wcel
    @85
    @19
    wcel
    wph
    @50
    @31
    simprl
    @10
    @9
    cF
    fvex
    snid
    @12
    @10
    cK
    @11
    opelxpi
    sylancl
    sseldd
    ralrimivva
    wph
    @83
    @87
    vp
    cK
    wph
    @35
    @78
    @83
    @87
    wb
    imasvscaf.f
    @79
    @82
    @86
    vy
    vq
    cV
    cF
    @38
    @10
    wceq
    @39
    @85
    @1
    @38
    @10
    @12
    opeq2
    eleq1d
    ralrn
    3syl
    ralbidv
    mpbird
    @80
    @82
    vx
    vp
    vy
    cK
    @25
    @4
    @39
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
