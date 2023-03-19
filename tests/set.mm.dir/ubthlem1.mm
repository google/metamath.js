include "cv.mm"
include "cfv.mm"
include "cnt.mm"
include "c0.mm"
include "wne.mm"
include "cn.mm"
include "wrex.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "crp.mm"
include "ccld.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "rzal.mm"
include "ralrimivw.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "ciin.mm"
include "iinrab.mm"
include "adantl.mm"
include "id.mm"
include "ccnv.mm"
include "cba.mm"
include "cima.mm"
include "cims.mm"
include "cmopn.mm"
include "cblo.mm"
include "sselda.mm"
include "ccn.mm"
include "eqid.mm"
include "ccbn.mm"
include "cnv.mm"
include "bnnv.mm"
include "ax-mp.mm"
include "blocn2.mm"
include "ctopon.mm"
include "wb.mm"
include "cxmt.mm"
include "cms.mm"
include "cme.mm"
include "cbncms.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "mp2b.mm"
include "mopntopon.mm"
include "imsxmet.mm"
include "iscncl.mm"
include "mp2an.mm"
include "sylib.mm"
include "syl.mm"
include "simpld.mm"
include "adantlr.mm"
include "ffvelrnda.mm"
include "biantrurd.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "syl6bbr.mm"
include "pm5.32da.mm"
include "fveq2d.mm"
include "a1i.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "cxr.mm"
include "cr.mm"
include "nnre.mm"
include "ad2antlr.mm"
include "rexrd.mm"
include "cn0v.mm"
include "nvzcl.mm"
include "nvnd.mm"
include "mpan.mm"
include "xmetsym.mm"
include "mp3an12.mm"
include "eqtr4d.mm"
include "rabbiia.mm"
include "blcld.mm"
include "simprd.mm"
include "imaeq2.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "iincld.mm"
include "syl2anr.mm"
include "eqeltrrd.mm"
include "ctop.mm"
include "mopntop.mm"
include "toponunii.mm"
include "topcld.mm"
include "pm2.61ne.mm"
include "fmptd.mm"
include "cpw.mm"
include "frn.mm"
include "cldss2.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "clt.mm"
include "wi.mm"
include "arch.mm"
include "simpr.mm"
include "ltle.mm"
include "syl2an.mm"
include "impr.mm"
include "adantr.mm"
include "an32s.mm"
include "nvcl.mm"
include "sylancr.mm"
include "simpllr.mm"
include "simplrl.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ralimdva.mm"
include "expr.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "eleq2d.mm"
include "ralbidv.mm"
include "syl6bb.mm"
include "bicomd.mm"
include "sylan9bbr.mm"
include "fnfvelrn.mm"
include "elssuni.mm"
include "sseld.mm"
include "sylan.mm"
include "sylbird.mm"
include "syl6d.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "dfss3.mm"
include "eqssd.mm"
include "ne0i.mm"
include "bcth2.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "wex.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "elpwid.mm"
include "ntrss3.mm"
include "cbl.mm"
include "ntropn.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "syl6sseqr.mm"
include "c2.mm"
include "cdiv.mm"
include "ntrss2.mm"
include "sstr2.mm"
include "syl5com.mm"
include "ad2antrr.mm"
include "w3a.mm"
include "jctil.mm"
include "rphalfcl.mm"
include "rpxrd.mm"
include "rpxr.mm"
include "rphalflt.mm"
include "3jca.mm"
include "blsscls2.mm"
include "breq2.mm"
include "rabbidv.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "ex.mm"
include "3syld.mm"
include "syldan.mm"
include "jcad.mm"
include "eximdv.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "reximdva.mm"

theorem ubthlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cT: class T
  let cU: class U
  let vk: setvar k
  let vn: setvar n
  let cJ: class J
  let cN: class N
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vc: setvar c
  let vd: setvar d
  let cK: class K
  let vm: setvar m
  let vu: setvar u
  let cP: class P
  let cR: class R
  assume ubth.1: |- X = ( BaseSet ` U )
  assume ubth.2: |- N = ( normCV ` W )
  assume ubthlem.3: |- D = ( IndMet ` U )
  assume ubthlem.4: |- J = ( MetOpen ` D )
  assume ubthlem.5: |- U e. CBan
  assume ubthlem.6: |- W e. NrmCVec
  assume ubthlem.7: |- ( ph -> T C_ ( U BLnOp W ) )
  assume ubthlem.8: |- ( ph -> A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c )
  assume ubthlem.9: |- A = ( k e. NN |-> { z e. X | A. t e. T ( N ` ( t ` z ) ) <_ k } )

  disjoint c k
  disjoint c n
  disjoint c r
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint c t
  disjoint D c
  disjoint k t
  disjoint D k
  disjoint n t
  disjoint D n
  disjoint r t
  disjoint D r
  disjoint t x
  disjoint t z
  disjoint D t
  disjoint D x
  disjoint D z
  disjoint J k
  disjoint J n
  disjoint t y
  disjoint J t
  disjoint J x
  disjoint J y
  disjoint N c
  disjoint N k
  disjoint N n
  disjoint N r
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint c ph
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint T c
  disjoint T k
  disjoint T n
  disjoint T r
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U c
  disjoint U n
  disjoint U r
  disjoint U t
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W c
  disjoint W n
  disjoint W r
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint X c
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint d k
  disjoint d t
  disjoint d x
  disjoint d z
  disjoint K d
  disjoint K k
  disjoint K t
  disjoint K x
  disjoint K z
  disjoint c d
  disjoint c m
  disjoint c u
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d u
  disjoint d y
  disjoint N d
  disjoint k m
  disjoint k u
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint N m
  disjoint n u
  disjoint r u
  disjoint t u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint N u
  disjoint P t
  disjoint P z
  disjoint R d
  disjoint R t
  disjoint R x
  disjoint R z
  disjoint T d
  disjoint T m
  disjoint T u
  disjoint U d
  disjoint W d
  disjoint X d
  disjoint X m
  assert |- ( ph -> E. n e. NN E. y e. X E. r e. RR+ { z e. X | ( y D z ) <_ r } C_ ( A ` n ) )

  proof
    wph
    vn
    cv
    #
    cA
    cfv
    #
    cJ
    cnt
    cfv
    cfv
    #
    c0
    wne
    #
    vn
    cn
    wrex
    #
    vy
    cv
    #
    vz
    cv
    #
    cD
    co
    #
    vr
    cv
    #
    cle
    wbr
    #
    vz
    cX
    crab
    #
    @1
    wss
    #
    vr
    crp
    wrex
    #
    vy
    cX
    wrex
    #
    vn
    cn
    wrex
    wph
    cn
    cJ
    ccld
    cfv
    #
    cA
    wf
    #
    cA
    crn
    #
    cuni
    #
    cX
    wceq
    #
    @4
    wph
    vk
    cn
    @6
    vt
    cv
    #
    cfv
    #
    cN
    cfv
    #
    vk
    cv
    #
    cle
    wbr
    #
    vt
    cT
    wral
    #
    vz
    cX
    crab
    #
    @14
    cA
    wph
    @22
    cn
    wcel
    #
    wa
    #
    @25
    @14
    wcel
    cX
    @14
    wcel
    #
    cT
    c0
    cT
    c0
    wceq
    #
    @25
    cX
    @14
    @29
    cX
    @25
    @29
    @24
    vz
    cX
    wral
    cX
    @25
    wceq
    @29
    @24
    vz
    cX
    @23
    vt
    cT
    rzal
    ralrimivw
    @24
    vz
    cX
    rabid2
    sylibr
    eqcomd
    eleq1d
    @27
    cT
    c0
    wne
    #
    wa
    vt
    cT
    @23
    vz
    cX
    crab
    #
    ciin
    #
    @25
    @14
    @30
    @32
    @25
    wceq
    @27
    @23
    vt
    vz
    cT
    cX
    iinrab
    adantl
    @30
    @30
    @31
    @14
    wcel
    #
    vt
    cT
    wral
    @32
    @14
    wcel
    @27
    @30
    id
    @27
    @33
    vt
    cT
    @27
    @19
    cT
    wcel
    #
    wa
    #
    @31
    @19
    ccnv
    #
    @5
    cN
    cfv
    #
    @22
    cle
    wbr
    #
    vy
    cW
    cba
    cfv
    #
    crab
    #
    cima
    #
    @14
    @35
    vx
    @31
    @41
    @35
    vx
    cv
    #
    cX
    wcel
    #
    @42
    @19
    cfv
    #
    cN
    cfv
    #
    @22
    cle
    wbr
    #
    wa
    #
    @43
    @44
    @40
    wcel
    #
    wa
    #
    @42
    @31
    wcel
    #
    @42
    @41
    wcel
    #
    @35
    @43
    @46
    @48
    @35
    @43
    wa
    #
    @46
    @44
    @39
    wcel
    #
    @46
    wa
    @48
    @52
    @53
    @46
    @35
    cX
    @39
    @42
    @19
    wph
    @34
    cX
    @39
    @19
    wf
    #
    @26
    wph
    @34
    wa
    #
    @54
    @36
    @42
    cima
    #
    @14
    wcel
    #
    vx
    cW
    cims
    cfv
    #
    cmopn
    cfv
    #
    ccld
    cfv
    #
    wral
    #
    @55
    @19
    cU
    cW
    cblo
    co
    #
    wcel
    #
    @54
    @61
    wa
    #
    wph
    cT
    @62
    @19
    ubthlem.7
    sselda
    @63
    @19
    cJ
    @59
    ccn
    co
    wcel
    #
    @64
    @62
    cD
    @58
    @19
    cU
    cJ
    @59
    cW
    ubthlem.3
    @58
    eqid
    #
    ubthlem.4
    @59
    eqid
    #
    @62
    eqid
    cU
    ccbn
    wcel
    #
    cU
    cnv
    wcel
    #
    ubthlem.5
    cU
    bnnv
    ax-mp
    #
    ubthlem.6
    blocn2
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @59
    @39
    ctopon
    cfv
    wcel
    #
    @65
    @64
    wb
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @71
    cD
    cX
    cms
    cfv
    wcel
    #
    cD
    cX
    cme
    cfv
    wcel
    @73
    @68
    @74
    ubthlem.5
    cD
    cU
    cX
    ubth.1
    ubthlem.3
    cbncms
    ax-mp
    #
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    mp2b
    #
    cD
    cJ
    cX
    ubthlem.4
    mopntopon
    ax-mp
    #
    @58
    @39
    cxmt
    cfv
    wcel
    #
    @72
    cW
    cnv
    wcel
    #
    @78
    ubthlem.6
    @58
    cW
    @39
    @39
    eqid
    #
    @66
    imsxmet
    ax-mp
    #
    @58
    @59
    @39
    @67
    mopntopon
    ax-mp
    vx
    @19
    cJ
    @59
    cX
    @39
    iscncl
    mp2an
    sylib
    syl
    #
    simpld
    #
    adantlr
    #
    ffvelrnda
    biantrurd
    @38
    @46
    vy
    @44
    @39
    @5
    @44
    wceq
    @37
    @45
    @22
    cle
    @5
    @44
    cN
    fveq2
    breq1d
    elrab
    syl6bbr
    pm5.32da
    @50
    @47
    wb
    @35
    @23
    @46
    vz
    @42
    cX
    @6
    @42
    wceq
    #
    @21
    @45
    @22
    cle
    @85
    @20
    @44
    cN
    @6
    @42
    @19
    fveq2
    fveq2d
    breq1d
    #
    elrab
    a1i
    @35
    @54
    @19
    cX
    wfn
    @51
    @49
    wb
    @84
    cX
    @39
    @19
    ffn
    cX
    @42
    @40
    @19
    elpreima
    3syl
    3bitr4d
    eqrdv
    @35
    @40
    @60
    wcel
    #
    @61
    @41
    @14
    wcel
    #
    @35
    @22
    cxr
    wcel
    #
    @87
    @35
    @22
    @26
    @22
    cr
    wcel
    #
    wph
    @34
    @22
    nnre
    #
    ad2antlr
    rexrd
    @78
    cW
    cn0v
    cfv
    #
    @39
    wcel
    #
    @89
    @87
    @81
    @79
    @93
    ubthlem.6
    cW
    @39
    @92
    @80
    @92
    eqid
    #
    nvzcl
    ax-mp
    #
    vy
    @58
    @92
    @22
    @40
    @59
    @39
    @67
    @38
    @92
    @5
    @58
    co
    #
    @22
    cle
    wbr
    vy
    @39
    @5
    @39
    wcel
    #
    @37
    @96
    @22
    cle
    @97
    @37
    @5
    @92
    @58
    co
    #
    @96
    @79
    @97
    @37
    @98
    wceq
    ubthlem.6
    @5
    @58
    cW
    cN
    @39
    @92
    @80
    @94
    ubth.2
    @66
    nvnd
    mpan
    @78
    @93
    @97
    @96
    @98
    wceq
    @81
    @95
    @92
    @5
    @58
    @39
    xmetsym
    mp3an12
    eqtr4d
    breq1d
    rabbiia
    blcld
    mp3an12
    syl
    wph
    @34
    @61
    @26
    @55
    @54
    @61
    @82
    simprd
    adantlr
    @57
    @88
    vx
    @40
    @60
    @42
    @40
    wceq
    @56
    @41
    @14
    @42
    @40
    @36
    imaeq2
    eleq1d
    rspcv
    sylc
    eqeltrd
    ralrimiva
    vt
    cT
    @31
    cJ
    iincld
    syl2anr
    eqeltrrd
    @28
    @27
    cJ
    ctop
    wcel
    #
    @28
    @73
    @99
    @76
    cD
    cJ
    cX
    ubthlem.4
    mopntop
    ax-mp
    #
    cJ
    cX
    cX
    cJ
    @77
    toponunii
    #
    topcld
    ax-mp
    a1i
    pm2.61ne
    ubthlem.9
    fmptd
    #
    wph
    @17
    cX
    wph
    @16
    cX
    cpw
    #
    wss
    @17
    cX
    wss
    wph
    @16
    @14
    @103
    wph
    @15
    @16
    @14
    wss
    @102
    cn
    @14
    cA
    frn
    syl
    cJ
    cX
    @101
    cldss2
    #
    syl6ss
    @16
    cX
    sspwuni
    sylib
    wph
    @42
    @17
    wcel
    #
    vx
    cX
    wral
    #
    cX
    @17
    wss
    wph
    @45
    vc
    cv
    #
    cle
    wbr
    #
    vt
    cT
    wral
    #
    vc
    cr
    wrex
    #
    vx
    cX
    wral
    @106
    ubthlem.8
    wph
    @110
    @105
    vx
    cX
    wph
    @43
    wa
    #
    @109
    @105
    vc
    cr
    @111
    @107
    cr
    wcel
    #
    wa
    #
    @107
    @22
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    @109
    @105
    wi
    #
    @112
    @115
    @111
    @107
    vk
    arch
    adantl
    @113
    @114
    @116
    vk
    cn
    @113
    @26
    wa
    @114
    @109
    @46
    vt
    cT
    wral
    #
    @105
    @113
    @26
    @114
    @109
    @117
    wi
    @113
    @26
    @114
    wa
    #
    wa
    #
    @108
    @46
    vt
    cT
    @119
    @34
    wa
    #
    @108
    @107
    @22
    cle
    wbr
    #
    @46
    @119
    @121
    @34
    @113
    @26
    @114
    @121
    @113
    @112
    @90
    @114
    @121
    wi
    @26
    @111
    @112
    simpr
    @91
    @107
    @22
    ltle
    syl2an
    impr
    adantr
    @120
    @45
    cr
    wcel
    #
    @112
    @90
    @108
    @121
    wa
    @46
    wi
    @113
    @34
    @122
    @118
    @111
    @34
    @122
    @112
    @111
    @34
    wa
    @79
    @53
    @122
    ubthlem.6
    wph
    @34
    @43
    @53
    @55
    cX
    @39
    @42
    @19
    @83
    ffvelrnda
    an32s
    @44
    cW
    cN
    @39
    @80
    ubth.2
    nvcl
    sylancr
    adantlr
    adantlr
    @111
    @112
    @118
    @34
    simpllr
    @120
    @26
    @90
    @113
    @26
    @114
    @34
    simplrl
    @91
    syl
    @45
    @107
    @22
    letr
    syl3anc
    mpan2d
    ralimdva
    expr
    @111
    @26
    @117
    @105
    wi
    @112
    @111
    @26
    wa
    @117
    @42
    @22
    cA
    cfv
    #
    wcel
    #
    @105
    @26
    @124
    @43
    @117
    wa
    #
    @111
    @117
    @26
    @124
    @42
    @25
    wcel
    @125
    @26
    @123
    @25
    @42
    @26
    @25
    cvv
    wcel
    @123
    @25
    wceq
    @24
    vz
    cX
    cX
    cU
    cba
    cfv
    cvv
    ubth.1
    cU
    cba
    fvex
    eqeltri
    rabex
    vk
    cn
    @25
    cvv
    cA
    ubthlem.9
    fvmpt2
    mpan2
    eleq2d
    @24
    @117
    vz
    @42
    cX
    @85
    @23
    @46
    vt
    cT
    @86
    ralbidv
    elrab
    syl6bb
    @111
    @117
    @125
    @111
    @43
    @117
    wph
    @43
    simpr
    biantrurd
    bicomd
    sylan9bbr
    @111
    cA
    cn
    wfn
    #
    @26
    @124
    @105
    wi
    wph
    @126
    @43
    wph
    @15
    @126
    @102
    cn
    @14
    cA
    ffn
    syl
    adantr
    @126
    @26
    wa
    #
    @123
    @17
    @42
    @127
    @123
    @16
    wcel
    @123
    @17
    wss
    cn
    @22
    cA
    fnfvelrn
    @123
    @16
    elssuni
    syl
    sseld
    sylan
    sylbird
    adantlr
    syl6d
    rexlimdva
    mpd
    rexlimdva
    ralimdva
    mpd
    vx
    cX
    @17
    dfss3
    sylibr
    eqssd
    @74
    cX
    c0
    wne
    #
    @15
    @18
    wa
    @4
    @75
    @69
    cU
    cn0v
    cfv
    #
    cX
    wcel
    @128
    @70
    cU
    cX
    @129
    ubth.1
    @129
    eqid
    nvzcl
    cX
    @129
    ne0i
    mp2b
    cD
    vn
    cJ
    cA
    cX
    ubthlem.4
    bcth2
    mpanl12
    syl2anc
    wph
    @3
    @13
    vn
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @5
    @2
    wcel
    #
    vy
    wex
    @5
    cX
    wcel
    #
    @12
    wa
    #
    vy
    wex
    @3
    @13
    @131
    @132
    @134
    vy
    @131
    @132
    @133
    @12
    @131
    @2
    cX
    @5
    @131
    @99
    @1
    cX
    wss
    #
    @2
    cX
    wss
    #
    @100
    wph
    @15
    @130
    @135
    @102
    @15
    @130
    wa
    #
    @1
    cX
    @137
    @14
    @103
    @1
    @104
    cn
    @14
    @0
    cA
    ffvelrn
    sseldi
    elpwid
    sylan
    #
    @1
    cJ
    cX
    @101
    ntrss3
    sylancr
    sseld
    @131
    @132
    @12
    @131
    @132
    wa
    @5
    @42
    cD
    cbl
    cfv
    co
    #
    @2
    wss
    #
    vx
    crp
    wrex
    #
    @12
    @131
    @2
    cJ
    wcel
    #
    @132
    @141
    @131
    @99
    @135
    @142
    @100
    @138
    @1
    cJ
    cX
    @101
    ntropn
    sylancr
    #
    @73
    @142
    @132
    @141
    @76
    vx
    @2
    cD
    @5
    cJ
    cX
    ubthlem.4
    mopni2
    mp3an1
    sylan
    @131
    @132
    @133
    @141
    @12
    wi
    @131
    @2
    cX
    @5
    @131
    @142
    @136
    @143
    @142
    @2
    cJ
    cuni
    cX
    @2
    cJ
    elssuni
    @101
    syl6sseqr
    syl
    sselda
    @131
    @133
    wa
    #
    @140
    @12
    vx
    crp
    @144
    @42
    crp
    wcel
    #
    wa
    #
    @140
    @139
    @1
    wss
    #
    @7
    @42
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    vz
    cX
    crab
    #
    @1
    wss
    #
    @12
    @131
    @140
    @147
    wi
    @133
    @145
    @131
    @2
    @1
    wss
    #
    @140
    @147
    @131
    @99
    @135
    @152
    @100
    @138
    @1
    cJ
    cX
    @101
    ntrss2
    sylancr
    @139
    @2
    @1
    sstr2
    syl5com
    ad2antrr
    @146
    @150
    @139
    wss
    #
    @147
    @151
    wi
    @144
    @73
    @133
    wa
    @148
    cxr
    wcel
    #
    @42
    cxr
    wcel
    #
    @148
    @42
    clt
    wbr
    #
    w3a
    @153
    @145
    @144
    @133
    @73
    @131
    @133
    simpr
    @76
    jctil
    @145
    @154
    @155
    @156
    @145
    @148
    @42
    rphalfcl
    #
    rpxrd
    @42
    rpxr
    @42
    rphalflt
    3jca
    vz
    cD
    @5
    @148
    @150
    @42
    cJ
    cX
    ubthlem.4
    @150
    eqid
    blsscls2
    syl2an
    @150
    @139
    @1
    sstr2
    syl
    @146
    @148
    crp
    wcel
    #
    @151
    @12
    wi
    @145
    @158
    @144
    @157
    adantl
    @158
    @151
    @12
    @11
    @151
    vr
    @148
    crp
    @8
    @148
    wceq
    #
    @10
    @150
    @1
    @159
    @9
    @149
    vz
    cX
    @8
    @148
    @7
    cle
    breq2
    rabbidv
    sseq1d
    rspcev
    ex
    syl
    3syld
    rexlimdva
    syldan
    mpd
    ex
    jcad
    eximdv
    vy
    @2
    n0
    @12
    vy
    cX
    df-rex
    3imtr4g
    reximdva
    mpd
end
