include "cmul.mm"
include "co.mm"
include "ccom.mm"
include "cdv.mm"
include "wbr.mm"
include "crest.mm"
include "cnt.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "wa.mm"
include "eqid.mm"
include "cc.mm"
include "sstrd.mm"
include "fssd.mm"
include "eldv.mm"
include "mpbid.mm"
include "simpld.mm"
include "wceq.mm"
include "cif.mm"
include "ctx.mm"
include "dvcl.mm"
include "mpdan.mm"
include "ad2antrr.mm"
include "wn.mm"
include "wf.mm"
include "adantr.mm"
include "eldifi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ffvelrnd.mm"
include "cdm.mm"
include "dvbss.mm"
include "wrel.mm"
include "reldv.mm"
include "releldm.mm"
include "sylancr.mm"
include "sseldd.mm"
include "subcld.mm"
include "ad2antlr.mm"
include "cc0.mm"
include "wne.mm"
include "simpr.mm"
include "subeq0ad.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "divcld.mm"
include "ifclda.mm"
include "dvlem.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cxp.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "txtopon.mm"
include "mp2an.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "anasss.mm"
include "eldifsni.mm"
include "ifnefalse.mm"
include "syl.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "cres.mm"
include "limcresi.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "difss.mm"
include "resmpt.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "syl5sseq.mm"
include "ccnp.mm"
include "dvcnp2.mm"
include "syl31anc.mm"
include "wb.mm"
include "cnplimc.mm"
include "syl2anc.mm"
include "simprd.mm"
include "mpteq2ia.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "iftrue.mm"
include "ad2antll.mm"
include "limcco.mm"
include "ccn.mm"
include "cop.mm"
include "mulcn.mm"
include "opelxpi.mm"
include "cncnpi.mm"
include "limccnp2.mm"
include "eqeq1d.mm"
include "mul01d.mm"
include "biimpar.mm"
include "subne0d.mm"
include "div0d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "syl5ibr.mm"
include "imp.mm"
include "3eqtr4d.mm"
include "dmdcan2d.mm"
include "ifbothda.mm"
include "fvco3.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"
include "eleqtrd.mm"
include "fco.mm"
include "mpbir2and.mm"

theorem dvcobr
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume dvco.f: |- ( ph -> F : X --> CC )
  assume dvco.x: |- ( ph -> X C_ S )
  assume dvco.g: |- ( ph -> G : Y --> X )
  assume dvco.y: |- ( ph -> Y C_ T )
  assume dvcobr.s: |- ( ph -> S C_ CC )
  assume dvcobr.t: |- ( ph -> T C_ CC )
  assume dvco.k: |- ( ph -> K e. V )
  assume dvco.l: |- ( ph -> L e. V )
  assume dvco.bf: |- ( ph -> ( G ` C ) ( S _D F ) K )
  assume dvco.bg: |- ( ph -> C ( T _D G ) L )
  assume dvco.j: |- J = ( TopOpen ` CCfld )


  assert |- ( ph -> C ( T _D ( F o. G ) ) ( K x. L ) )

  proof
    wph
    cC
    cK
    cL
    cmul
    co
    #
    cT
    cF
    cG
    ccom
    #
    cdv
    co
    wbr
    cC
    cY
    cJ
    cT
    crest
    co
    #
    cnt
    cfv
    cfv
    wcel
    #
    @0
    vz
    cY
    cC
    csn
    #
    cdif
    #
    vz
    cv
    #
    @1
    cfv
    #
    cC
    @1
    cfv
    #
    cmin
    co
    #
    @6
    cC
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cC
    climc
    co
    #
    wcel
    wph
    @3
    cL
    vz
    @5
    @6
    cG
    cfv
    #
    cC
    cG
    cfv
    #
    cmin
    co
    #
    @10
    cdiv
    co
    #
    cmpt
    #
    cC
    climc
    co
    wcel
    #
    wph
    cC
    cL
    cT
    cG
    cdv
    co
    #
    wbr
    #
    @3
    @19
    wa
    dvco.bg
    wph
    vz
    cY
    cC
    cL
    cT
    @2
    cG
    @18
    cJ
    @2
    eqid
    #
    dvco.j
    @18
    eqid
    dvcobr.t
    wph
    cY
    cX
    cc
    cG
    dvco.g
    wph
    cX
    cS
    cc
    dvco.x
    dvcobr.s
    sstrd
    #
    fssd
    #
    dvco.y
    eldv
    mpbid
    #
    simpld
    wph
    @0
    vz
    @5
    @14
    @15
    wceq
    #
    cK
    @14
    cF
    cfv
    #
    @15
    cF
    cfv
    #
    cmin
    co
    #
    @16
    cdiv
    co
    #
    cif
    #
    @17
    cmul
    co
    #
    cmpt
    #
    cC
    climc
    co
    @13
    wph
    vz
    @5
    cC
    cK
    cL
    @31
    @17
    cmul
    cJ
    cJ
    ctx
    co
    #
    cJ
    cc
    cc
    wph
    @6
    @5
    wcel
    #
    wa
    #
    @26
    cK
    @30
    cc
    wph
    cK
    cc
    wcel
    #
    @35
    @26
    wph
    @15
    cK
    cS
    cF
    cdv
    co
    wbr
    #
    @37
    dvco.bf
    wph
    cX
    @15
    cK
    cS
    cF
    dvcobr.s
    dvco.f
    dvco.x
    dvcl
    mpdan
    #
    ad2antrr
    #
    @36
    @26
    wn
    #
    wa
    #
    @29
    @16
    @42
    @27
    @28
    @36
    @27
    cc
    wcel
    @41
    @36
    cX
    cc
    @14
    cF
    wph
    cX
    cc
    cF
    wf
    #
    @35
    dvco.f
    adantr
    #
    wph
    cY
    cX
    cG
    wf
    #
    @6
    cY
    wcel
    #
    @14
    cX
    wcel
    #
    @35
    dvco.g
    @6
    cY
    @4
    eldifi
    #
    cY
    cX
    @6
    cG
    ffvelrn
    syl2an
    #
    ffvelrnd
    #
    adantr
    @36
    @28
    cc
    wcel
    @41
    @36
    cX
    cc
    @15
    cF
    @44
    @36
    cY
    cX
    cC
    cG
    wph
    @45
    @35
    dvco.g
    adantr
    wph
    cC
    cY
    wcel
    #
    @35
    wph
    @20
    cdm
    #
    cY
    cC
    wph
    cY
    cT
    cG
    dvcobr.t
    @24
    dvco.y
    dvbss
    wph
    @20
    wrel
    @21
    cC
    @52
    wcel
    #
    cT
    cG
    reldv
    dvco.bg
    cC
    cL
    @20
    releldm
    sylancr
    #
    sseldd
    #
    adantr
    #
    ffvelrnd
    #
    ffvelrnd
    #
    adantr
    subcld
    #
    @42
    @14
    @15
    @42
    cY
    cc
    @6
    cG
    wph
    cY
    cc
    cG
    wf
    #
    @35
    @41
    @24
    ad2antrr
    #
    @35
    @46
    wph
    @41
    @48
    ad2antlr
    ffvelrnd
    #
    @42
    cY
    cc
    cC
    cG
    @61
    wph
    @51
    @35
    @41
    @55
    ad2antrr
    ffvelrnd
    #
    subcld
    #
    @42
    @16
    cc0
    wne
    @41
    @36
    @41
    simpr
    @42
    @26
    @16
    cc0
    @42
    @14
    @15
    @62
    @63
    subeq0ad
    necon3abid
    mpbird
    #
    divcld
    ifclda
    wph
    @6
    cC
    cY
    cG
    @24
    wph
    cY
    cT
    cc
    dvco.y
    dvcobr.t
    sstrd
    #
    @55
    dvlem
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    #
    @67
    dvco.j
    @34
    cc
    cc
    cxp
    #
    crest
    co
    #
    @34
    @34
    @68
    ctopon
    cfv
    #
    wcel
    #
    @69
    @34
    wceq
    cJ
    cc
    ctopon
    cfv
    wcel
    #
    @72
    @71
    cJ
    dvco.j
    cnfldtopon
    #
    @73
    cJ
    cJ
    cc
    cc
    txtopon
    mp2an
    #
    @34
    @70
    @68
    @68
    @34
    @74
    toponunii
    #
    restid
    ax-mp
    eqcomi
    wph
    vz
    vy
    @5
    cX
    @15
    csn
    cdif
    #
    @15
    cK
    @14
    vy
    cv
    #
    @15
    wceq
    #
    cK
    @77
    cF
    cfv
    #
    @28
    cmin
    co
    #
    @77
    @15
    cmin
    co
    #
    cdiv
    co
    #
    cif
    #
    @31
    cC
    wph
    @35
    @14
    @15
    wne
    #
    @14
    @76
    wcel
    #
    @36
    @84
    wa
    @47
    @84
    wa
    @85
    @36
    @47
    @84
    @49
    anim1i
    @14
    cX
    @15
    eldifsn
    sylibr
    anasss
    wph
    @77
    @76
    wcel
    #
    wa
    @83
    @82
    cc
    @86
    @83
    @82
    wceq
    #
    wph
    @86
    @77
    @15
    wne
    @87
    @77
    cX
    @15
    eldifsni
    @77
    @15
    cK
    @82
    ifnefalse
    syl
    #
    adantl
    wph
    @77
    @15
    cX
    cF
    dvco.f
    @23
    wph
    cY
    cX
    cC
    cG
    dvco.g
    @55
    ffvelrnd
    dvlem
    eqeltrd
    wph
    cG
    cC
    climc
    co
    #
    vz
    @5
    @14
    cmpt
    #
    cC
    climc
    co
    #
    @15
    wph
    cG
    @5
    cres
    #
    cC
    climc
    co
    @89
    @91
    cC
    @5
    cG
    limcresi
    wph
    @92
    @90
    cC
    climc
    wph
    @92
    vz
    cY
    @14
    cmpt
    #
    @5
    cres
    #
    @90
    wph
    cG
    @93
    @5
    wph
    vz
    cY
    cX
    cG
    dvco.g
    feqmptd
    reseq1d
    @5
    cY
    wss
    @94
    @90
    wceq
    cY
    @4
    difss
    vz
    cY
    @5
    @14
    resmpt
    ax-mp
    syl6eq
    oveq1d
    syl5sseq
    wph
    @60
    @15
    @89
    wcel
    #
    wph
    cG
    cC
    cJ
    cY
    crest
    co
    #
    cJ
    ccnp
    co
    cfv
    wcel
    #
    @60
    @95
    wa
    #
    wph
    cT
    cc
    wss
    @60
    cY
    cT
    wss
    @53
    @97
    dvcobr.t
    @24
    dvco.y
    @54
    cY
    cC
    cT
    cG
    @96
    cJ
    @96
    eqid
    #
    dvco.j
    dvcnp2
    syl31anc
    wph
    cY
    cc
    wss
    #
    @51
    @97
    @98
    wb
    @66
    @55
    cY
    cC
    cG
    @96
    cJ
    dvco.j
    @99
    cnplimc
    syl2anc
    mpbid
    simprd
    sseldd
    wph
    cK
    vy
    @76
    @82
    cmpt
    #
    @15
    climc
    co
    #
    vy
    @76
    @83
    cmpt
    #
    @15
    climc
    co
    wph
    @15
    cX
    cJ
    cS
    crest
    co
    #
    cnt
    cfv
    cfv
    wcel
    #
    cK
    @102
    wcel
    #
    wph
    @38
    @105
    @106
    wa
    dvco.bf
    wph
    vy
    cX
    @15
    cK
    cS
    @104
    cF
    @101
    cJ
    @104
    eqid
    dvco.j
    @101
    eqid
    dvcobr.s
    dvco.f
    dvco.x
    eldv
    mpbid
    simprd
    @103
    @101
    @15
    climc
    vy
    @76
    @83
    @82
    @88
    mpteq2ia
    oveq1i
    syl6eleqr
    @77
    @14
    wceq
    #
    @78
    @26
    @82
    @30
    cK
    @77
    @14
    @15
    eqeq1
    @107
    @80
    @29
    @81
    @16
    cdiv
    @107
    @79
    @27
    @28
    cmin
    @77
    @14
    cF
    fveq2
    oveq1d
    @77
    @14
    @15
    cmin
    oveq1
    oveq12d
    ifbieq2d
    @26
    @31
    cK
    wceq
    wph
    @35
    @26
    cK
    @30
    iftrue
    ad2antll
    limcco
    wph
    @3
    @19
    @25
    simprd
    wph
    cmul
    @34
    cJ
    ccn
    co
    wcel
    cK
    cL
    cop
    #
    @68
    wcel
    #
    cmul
    @108
    @34
    cJ
    ccnp
    co
    cfv
    wcel
    cJ
    dvco.j
    mulcn
    wph
    @37
    cL
    cc
    wcel
    #
    @109
    @39
    wph
    @21
    @110
    dvco.bg
    wph
    cY
    cC
    cL
    cT
    cG
    dvcobr.t
    @24
    dvco.y
    dvcl
    mpdan
    cK
    cL
    cc
    cc
    opelxpi
    syl2anc
    @108
    cmul
    @34
    cJ
    @68
    @75
    cncnpi
    sylancr
    limccnp2
    wph
    @33
    @12
    cC
    climc
    wph
    vz
    @5
    @32
    @11
    @36
    @32
    @29
    @10
    cdiv
    co
    #
    @11
    @26
    cK
    @17
    cmul
    co
    #
    @111
    wceq
    @30
    @17
    cmul
    co
    #
    @111
    wceq
    @32
    @111
    wceq
    @36
    cK
    @30
    cK
    @31
    wceq
    @112
    @32
    @111
    cK
    @31
    @17
    cmul
    oveq1
    eqeq1d
    @30
    @31
    wceq
    @113
    @32
    @111
    @30
    @31
    @17
    cmul
    oveq1
    eqeq1d
    @36
    @26
    wa
    #
    cK
    cc0
    cmul
    co
    cc0
    @112
    @111
    @114
    cK
    @40
    mul01d
    @114
    @17
    cc0
    cK
    cmul
    @114
    @17
    cc0
    @10
    cdiv
    co
    #
    cc0
    @114
    @16
    cc0
    @10
    cdiv
    @36
    @16
    cc0
    wceq
    @26
    @36
    @14
    @15
    @36
    cX
    cc
    @14
    wph
    cX
    cc
    wss
    @35
    @23
    adantr
    #
    @49
    sseldd
    @36
    cX
    cc
    @15
    @116
    @57
    sseldd
    subeq0ad
    biimpar
    oveq1d
    @36
    @115
    cc0
    wceq
    @26
    @36
    @10
    @36
    @6
    cC
    @36
    cY
    cc
    @6
    wph
    @100
    @35
    @66
    adantr
    #
    @35
    @46
    wph
    @48
    adantl
    sseldd
    #
    @36
    cY
    cc
    cC
    @117
    @56
    sseldd
    #
    subcld
    #
    @36
    @6
    cC
    @118
    @119
    @35
    @6
    cC
    wne
    wph
    @6
    cY
    cC
    eldifsni
    adantl
    subne0d
    #
    div0d
    adantr
    #
    eqtrd
    oveq2d
    @114
    @111
    @115
    cc0
    @114
    @29
    cc0
    @10
    cdiv
    @36
    @26
    @29
    cc0
    wceq
    #
    @26
    @123
    @36
    @27
    @28
    wceq
    @14
    @15
    cF
    fveq2
    @36
    @27
    @28
    @50
    @58
    subeq0ad
    syl5ibr
    imp
    oveq1d
    @122
    eqtrd
    3eqtr4d
    @42
    @29
    @16
    @10
    @59
    @64
    @36
    @10
    cc
    wcel
    @41
    @120
    adantr
    @65
    @36
    @10
    cc0
    wne
    @41
    @121
    adantr
    dmdcan2d
    ifbothda
    @36
    @9
    @29
    @10
    cdiv
    @36
    @7
    @27
    @8
    @28
    cmin
    wph
    @45
    @46
    @7
    @27
    wceq
    @35
    dvco.g
    @48
    cY
    cX
    @6
    cF
    cG
    fvco3
    syl2an
    wph
    @8
    @28
    wceq
    #
    @35
    wph
    @45
    @51
    @124
    dvco.g
    @55
    cY
    cX
    cC
    cF
    cG
    fvco3
    syl2anc
    adantr
    oveq12d
    oveq1d
    eqtr4d
    mpteq2dva
    oveq1d
    eleqtrd
    wph
    vz
    cY
    cC
    @0
    cT
    @2
    @1
    @12
    cJ
    @22
    dvco.j
    @12
    eqid
    dvcobr.t
    wph
    @43
    @45
    cY
    cc
    @1
    wf
    dvco.f
    dvco.g
    cY
    cX
    cc
    cF
    cG
    fco
    syl2anc
    dvco.y
    eldv
    mpbir2and
end
