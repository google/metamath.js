include "cfv.mm"
include "c1.mm"
include "cdv.mm"
include "co.mm"
include "cdiv.mm"
include "ccnv.mm"
include "wbr.mm"
include "cnt.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "climc.mm"
include "wf1o.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "ctop.mm"
include "wceq.mm"
include "ctopon.mm"
include "crest.mm"
include "cc.mm"
include "wss.mm"
include "cnfldtopon.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "topontop.mm"
include "isopn3i.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "wne.mm"
include "wa.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "eldifi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "anasss.mm"
include "cdm.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "sstrd.mm"
include "sselda.mm"
include "sylan2.mm"
include "sseldd.mm"
include "adantr.mm"
include "subcld.mm"
include "toponss.mm"
include "fssd.mm"
include "cc0.mm"
include "eldifsni.mm"
include "adantl.mm"
include "subeq0ad.mm"
include "wf1.mm"
include "wb.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "bitrd.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "divcld.mm"
include "cres.mm"
include "limcresi.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "difss.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "syl5sseq.mm"
include "f1ocnvfv1.mm"
include "cnlimci.mm"
include "eqeltrrd.mm"
include "ccom.mm"
include "dvlem.mm"
include "subne0d.mm"
include "divne0d.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "fmptd.mm"
include "a1i.mm"
include "wfun.mm"
include "dvfg.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "4syl.mm"
include "mpbid.mm"
include "eldv.mm"
include "simprd.mm"
include "ccn.mm"
include "ccnp.mm"
include "mp2an.mm"
include "1cnd.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "ctx.mm"
include "divcn.mm"
include "cnmpt12f.mm"
include "feq2d.mm"
include "crn.mm"
include "wn.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "nelne2.mm"
include "toponunii.mm"
include "cncnpi.mm"
include "limccnp.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqidd.mm"
include "fmptco.mm"
include "recdivd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "3eltr3d.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "necomd.mm"
include "f1ocnvfvb.mm"
include "syl3anc.mm"
include "necon3abid.mm"
include "pm2.21d.mm"
include "impr.mm"
include "limcco.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "f1ocnvfv2.mm"
include "eleqtrd.mm"
include "mpbir2and.mm"

theorem dvcnvlem
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvcnv.j: |- J = ( TopOpen ` CCfld )
  assume dvcnv.k: |- K = ( J |`t S )
  assume dvcnv.s: |- ( ph -> S e. { RR , CC } )
  assume dvcnv.y: |- ( ph -> Y e. K )
  assume dvcnv.f: |- ( ph -> F : X -1-1-onto-> Y )
  assume dvcnv.i: |- ( ph -> `' F e. ( Y -cn-> X ) )
  assume dvcnv.d: |- ( ph -> dom ( S _D F ) = X )
  assume dvcnv.z: |- ( ph -> -. 0 e. ran ( S _D F ) )
  assume dvcnv.c: |- ( ph -> C e. X )


  assert |- ( ph -> ( F ` C ) ( S _D `' F ) ( 1 / ( ( S _D F ) ` C ) ) )

  proof
    wph
    cC
    cF
    cfv
    #
    c1
    cC
    cS
    cF
    cdv
    co
    #
    cfv
    #
    cdiv
    co
    #
    cS
    cF
    ccnv
    #
    cdv
    co
    wbr
    @0
    cY
    cK
    cnt
    cfv
    #
    cfv
    #
    wcel
    @3
    vz
    cY
    @0
    csn
    #
    cdif
    #
    vz
    cv
    #
    @4
    cfv
    #
    @0
    @4
    cfv
    #
    cmin
    co
    #
    @9
    @0
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @0
    climc
    co
    #
    wcel
    wph
    @0
    cY
    @6
    wph
    cX
    cY
    cC
    cF
    wph
    cX
    cY
    cF
    wf1o
    #
    cX
    cY
    cF
    wf
    dvcnv.f
    cX
    cY
    cF
    f1of
    syl
    #
    dvcnv.c
    ffvelrnd
    #
    wph
    cK
    ctop
    wcel
    #
    cY
    cK
    wcel
    #
    @6
    cY
    wceq
    wph
    cK
    cS
    ctopon
    cfv
    #
    wcel
    #
    @20
    wph
    cK
    cJ
    cS
    crest
    co
    #
    @22
    dvcnv.k
    wph
    cJ
    cc
    ctopon
    cfv
    wcel
    #
    cS
    cc
    wss
    #
    @24
    @22
    wcel
    cJ
    dvcnv.j
    cnfldtopon
    #
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @26
    dvcnv.s
    cS
    recnprss
    syl
    #
    cS
    cJ
    cc
    resttopon
    sylancr
    syl5eqel
    #
    cS
    cK
    topontop
    syl
    dvcnv.y
    cY
    cK
    isopn3i
    syl2anc
    eleqtrrd
    wph
    @3
    vz
    @8
    @10
    cC
    cmin
    co
    #
    @10
    cF
    cfv
    #
    @0
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @0
    climc
    co
    @16
    wph
    vz
    vy
    @8
    cX
    cC
    csn
    #
    cdif
    #
    cC
    @3
    @10
    vy
    cv
    #
    cC
    cmin
    co
    #
    @38
    cF
    cfv
    #
    @0
    cmin
    co
    #
    cdiv
    co
    #
    @34
    @0
    wph
    @9
    @8
    wcel
    #
    @10
    cC
    wne
    #
    @10
    @37
    wcel
    #
    wph
    @43
    wa
    #
    @44
    wa
    @10
    cX
    wcel
    #
    @44
    wa
    @45
    @46
    @47
    @44
    wph
    cY
    cX
    @4
    wf
    #
    @9
    cY
    wcel
    #
    @47
    @43
    wph
    @17
    cY
    cX
    @4
    wf1o
    @48
    dvcnv.f
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @4
    f1of
    3syl
    #
    @9
    cY
    @7
    eldifi
    #
    cY
    cX
    @9
    @4
    ffvelrn
    syl2an
    anim1i
    @10
    cX
    cC
    eldifsn
    sylibr
    anasss
    wph
    @38
    @37
    wcel
    #
    wa
    #
    @39
    @41
    @53
    @38
    cC
    @52
    wph
    @38
    cX
    wcel
    #
    @38
    cc
    wcel
    @38
    cX
    @36
    eldifi
    #
    wph
    cX
    cc
    @38
    wph
    cX
    cS
    cc
    wph
    cX
    @1
    cdm
    #
    cS
    dvcnv.d
    cS
    cF
    dvbsss
    syl6eqssr
    #
    @29
    sstrd
    #
    sselda
    sylan2
    #
    wph
    cC
    cc
    wcel
    @52
    wph
    cS
    cc
    cC
    @29
    wph
    cX
    cS
    cC
    @57
    dvcnv.c
    sseldd
    sseldd
    adantr
    #
    subcld
    #
    @53
    @40
    @0
    wph
    cX
    cc
    cF
    wf
    @54
    @40
    cc
    wcel
    @52
    wph
    cX
    cY
    cc
    cF
    @18
    wph
    cY
    cS
    cc
    wph
    @23
    @21
    cY
    cS
    wss
    @30
    dvcnv.y
    cY
    cK
    cS
    toponss
    syl2anc
    #
    @29
    sstrd
    #
    fssd
    #
    @55
    cX
    cc
    @38
    cF
    ffvelrn
    syl2an
    #
    wph
    @0
    cc
    wcel
    @52
    wph
    cY
    cc
    @0
    @63
    @19
    sseldd
    adantr
    #
    subcld
    #
    @53
    @41
    cc0
    wne
    @38
    cC
    wne
    #
    @52
    @68
    wph
    @38
    cX
    cC
    eldifsni
    adantl
    #
    @53
    @41
    cc0
    @38
    cC
    @53
    @41
    cc0
    wceq
    @40
    @0
    wceq
    #
    @38
    cC
    wceq
    #
    @53
    @40
    @0
    @65
    @66
    subeq0ad
    @53
    cX
    cY
    cF
    wf1
    #
    @54
    cC
    cX
    wcel
    #
    @70
    @71
    wb
    wph
    @72
    @52
    wph
    @17
    @72
    dvcnv.f
    cX
    cY
    cF
    f1of1
    syl
    adantr
    @52
    @54
    wph
    @55
    adantl
    wph
    @73
    @52
    dvcnv.c
    adantr
    cX
    cY
    @38
    cC
    cF
    f1fveq
    syl12anc
    bitrd
    necon3bid
    mpbird
    #
    divcld
    wph
    @4
    @0
    climc
    co
    #
    vz
    @8
    @10
    cmpt
    #
    @0
    climc
    co
    #
    cC
    wph
    @4
    @8
    cres
    #
    @0
    climc
    co
    @75
    @77
    @0
    @8
    @4
    limcresi
    wph
    @78
    @76
    @0
    climc
    wph
    @78
    vz
    cY
    @10
    cmpt
    #
    @8
    cres
    #
    @76
    wph
    @4
    @79
    @8
    wph
    vz
    cY
    cX
    @4
    @50
    feqmptd
    reseq1d
    @8
    cY
    wss
    @80
    @76
    wceq
    cY
    @7
    difss
    vz
    cY
    @8
    @10
    resmpt
    ax-mp
    syl6eq
    oveq1d
    syl5sseq
    wph
    @11
    cC
    @75
    wph
    @17
    @73
    @11
    cC
    wceq
    dvcnv.f
    dvcnv.c
    cX
    cY
    cC
    cF
    f1ocnvfv1
    syl2anc
    #
    wph
    cY
    @0
    cX
    @4
    dvcnv.i
    @19
    cnlimci
    eqeltrrd
    sseldd
    wph
    @2
    vx
    cc
    cc0
    csn
    #
    cdif
    #
    c1
    vx
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cfv
    #
    @86
    vy
    @37
    @41
    @39
    cdiv
    co
    #
    cmpt
    #
    ccom
    #
    cC
    climc
    co
    @3
    vy
    @37
    @42
    cmpt
    #
    cC
    climc
    co
    wph
    @37
    cC
    @2
    @83
    @89
    @86
    cJ
    @83
    crest
    co
    #
    cJ
    wph
    vy
    @37
    @88
    @83
    @89
    @53
    @88
    cc
    wcel
    @88
    cc0
    wne
    @88
    @83
    wcel
    wph
    @38
    cC
    cX
    cF
    @64
    @58
    dvcnv.c
    dvlem
    @53
    @41
    @39
    @67
    @61
    @74
    @53
    @38
    cC
    @59
    @60
    @69
    subne0d
    #
    divne0d
    @88
    cc
    cc0
    eldifsn
    sylanbrc
    #
    @89
    eqid
    #
    fmptd
    @83
    cc
    wss
    #
    wph
    cc
    @82
    difss
    #
    a1i
    dvcnv.j
    @92
    eqid
    #
    wph
    cC
    cX
    @5
    cfv
    wcel
    #
    @2
    @89
    cC
    climc
    co
    wcel
    #
    wph
    cC
    @2
    @1
    wbr
    #
    @99
    @100
    wa
    wph
    cC
    @56
    wcel
    #
    @101
    wph
    cC
    cX
    @56
    dvcnv.c
    dvcnv.d
    eleqtrrd
    #
    wph
    @28
    @56
    cc
    @1
    wf
    #
    @1
    wfun
    @102
    @101
    wb
    dvcnv.s
    cS
    cF
    dvfg
    #
    @56
    cc
    @1
    ffun
    cC
    @1
    funfvbrb
    4syl
    mpbid
    wph
    vy
    cX
    cC
    @2
    cS
    cK
    cF
    @89
    cJ
    dvcnv.k
    dvcnv.j
    @95
    @29
    @64
    @57
    eldv
    mpbid
    simprd
    wph
    @86
    @92
    cJ
    ccn
    co
    wcel
    @2
    @83
    wcel
    #
    @86
    @2
    @92
    cJ
    ccnp
    co
    cfv
    wcel
    wph
    vx
    c1
    @84
    cdiv
    @92
    cJ
    @92
    cJ
    @83
    @92
    @83
    ctopon
    cfv
    wcel
    #
    wph
    @25
    @96
    @107
    @27
    @97
    @83
    cJ
    cc
    resttopon
    mp2an
    #
    a1i
    #
    wph
    vx
    c1
    @92
    cJ
    @83
    cc
    @109
    @25
    wph
    @27
    a1i
    wph
    1cnd
    cnmptc
    wph
    vx
    @92
    @83
    @109
    cnmptid
    cdiv
    cJ
    @92
    ctx
    co
    cJ
    ccn
    co
    wcel
    wph
    cJ
    @92
    dvcnv.j
    @98
    divcn
    a1i
    cnmpt12f
    wph
    @2
    cc
    wcel
    @2
    cc0
    wne
    #
    @106
    wph
    cX
    cc
    cC
    @1
    wph
    @104
    cX
    cc
    @1
    wf
    wph
    @28
    @104
    dvcnv.s
    @105
    syl
    #
    wph
    @56
    cX
    cc
    @1
    dvcnv.d
    feq2d
    mpbid
    dvcnv.c
    ffvelrnd
    wph
    @2
    @1
    crn
    #
    wcel
    #
    cc0
    @112
    wcel
    wn
    @110
    wph
    @1
    @56
    wfn
    #
    @102
    @113
    wph
    @104
    @114
    @111
    @56
    cc
    @1
    ffn
    syl
    @103
    @56
    cC
    @1
    fnfvelrn
    syl2anc
    dvcnv.z
    @2
    cc0
    @112
    nelne2
    syl2anc
    @2
    cc
    cc0
    eldifsn
    sylanbrc
    #
    @2
    @86
    @92
    cJ
    @83
    @83
    @92
    @108
    toponunii
    cncnpi
    syl2anc
    limccnp
    wph
    @106
    @87
    @3
    wceq
    @115
    vx
    @2
    @85
    @3
    @83
    @86
    @84
    @2
    c1
    cdiv
    oveq2
    @86
    eqid
    c1
    @2
    cdiv
    ovex
    fvmpt
    syl
    wph
    @90
    @91
    cC
    climc
    wph
    @90
    vy
    @37
    c1
    @88
    cdiv
    co
    #
    cmpt
    @91
    wph
    vy
    vx
    @37
    @83
    @88
    @85
    @116
    @89
    @86
    @94
    wph
    @89
    eqidd
    wph
    @86
    eqidd
    @84
    @88
    c1
    cdiv
    oveq2
    fmptco
    wph
    vy
    @37
    @116
    @42
    @53
    @41
    @39
    @67
    @61
    @74
    @93
    recdivd
    mpteq2dva
    eqtrd
    oveq1d
    3eltr3d
    @38
    @10
    wceq
    #
    @39
    @31
    @41
    @33
    cdiv
    @38
    @10
    cC
    cmin
    oveq1
    @117
    @40
    @32
    @0
    cmin
    @38
    @10
    cF
    fveq2
    oveq1d
    oveq12d
    wph
    @43
    @10
    cC
    wceq
    #
    @34
    @3
    wceq
    #
    @46
    @118
    @119
    @46
    @0
    @9
    wne
    @118
    wn
    @46
    @9
    @0
    @43
    @9
    @0
    wne
    wph
    @9
    cY
    @0
    eldifsni
    adantl
    necomd
    @46
    @118
    @0
    @9
    @46
    @17
    @73
    @49
    @0
    @9
    wceq
    @118
    wb
    wph
    @17
    @43
    dvcnv.f
    adantr
    wph
    @73
    @43
    dvcnv.c
    adantr
    @43
    @49
    wph
    @51
    adantl
    cX
    cY
    cC
    @9
    cF
    f1ocnvfvb
    syl3anc
    necon3abid
    mpbid
    pm2.21d
    impr
    limcco
    wph
    @35
    @15
    @0
    climc
    wph
    vz
    @8
    @34
    @14
    @46
    @31
    @12
    @33
    @13
    cdiv
    @46
    cC
    @11
    @10
    cmin
    wph
    cC
    @11
    wceq
    @43
    wph
    @11
    cC
    @81
    eqcomd
    adantr
    oveq2d
    @46
    @32
    @9
    @0
    cmin
    wph
    @17
    @49
    @32
    @9
    wceq
    @43
    dvcnv.f
    @51
    cX
    cY
    @9
    cF
    f1ocnvfv2
    syl2an
    oveq1d
    oveq12d
    mpteq2dva
    oveq1d
    eleqtrd
    wph
    vz
    cY
    @0
    @3
    cS
    cK
    @4
    @15
    cJ
    dvcnv.k
    dvcnv.j
    @15
    eqid
    @29
    wph
    cY
    cX
    cc
    @4
    @50
    @58
    fssd
    @62
    eldv
    mpbir2and
end
