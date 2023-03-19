include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cnmoo.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "nnrpd.mm"
include "rpaddcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "wa.mm"
include "cnmcv.mm"
include "c1.mm"
include "wi.mm"
include "cns.mm"
include "cpv.mm"
include "crab.mm"
include "wss.mm"
include "rabss.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "cnv.mm"
include "ccbn.mm"
include "bnnv.mm"
include "ax-mp.mm"
include "a1i.mm"
include "cc.mm"
include "crp.mm"
include "rpcnd.mm"
include "simpr.mm"
include "eqid.mm"
include "nvscl.mm"
include "syl3anc.mm"
include "nvgcl.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "sylc.mm"
include "cmul.mm"
include "cnsb.mm"
include "cxmt.mm"
include "cms.mm"
include "cme.mm"
include "cbncms.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "mp2b.mm"
include "xmetsym.mm"
include "imsdval.mm"
include "nvpncan2.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "cc0.mm"
include "rprege0d.mm"
include "nvsge0.mm"
include "eqtrd.mm"
include "mulid1d.mm"
include "eqcomd.mm"
include "breq12d.mm"
include "nvcl.mm"
include "mpan.mm"
include "adantl.mm"
include "1red.mm"
include "lemul2d.mm"
include "bitr4d.mm"
include "wb.mm"
include "cn.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "cba.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "elrab.mm"
include "syl6bb.mm"
include "3imtr3d.mm"
include "rsp.mm"
include "com12.mm"
include "ad2antlr.mm"
include "xmet0.mm"
include "sylancr.mm"
include "rpge0d.mm"
include "eqbrtrd.mm"
include "sylanbrc.mm"
include "sseldd.mm"
include "eleqtrd.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "adantr.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "ccld.mm"
include "cims.mm"
include "cmopn.mm"
include "cblo.mm"
include "sselda.mm"
include "ccn.mm"
include "blocn2.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "imsxmet.mm"
include "iscncl.mm"
include "mp2an.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "nnred.mm"
include "le2add.mm"
include "syl22anc.mm"
include "mpan2d.mm"
include "clno.mm"
include "bloln.mm"
include "mp3an12.mm"
include "lnosub.mm"
include "syl32anc.mm"
include "lnomul.mm"
include "3eqtr3d.mm"
include "ffvelrnda.mm"
include "nvmtri.mm"
include "eqbrtrrd.mm"
include "remulcld.mm"
include "readdcld.mm"
include "letr.mm"
include "mpand.mm"
include "syld.mm"
include "lemuldiv2d.mm"
include "sylibd.mm"
include "adantld.mm"
include "ralrimiva.mm"
include "cxr.mm"
include "rpxrd.mm"
include "nmoubi.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "rspcev.mm"

theorem ubthlem2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let vk: setvar k
  let cJ: class J
  let cK: class K
  let cN: class N
  let cW: class W
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vm: setvar m
  let vu: setvar u
  assume ubth.1: |- X = ( BaseSet ` U )
  assume ubth.2: |- N = ( normCV ` W )
  assume ubthlem.3: |- D = ( IndMet ` U )
  assume ubthlem.4: |- J = ( MetOpen ` D )
  assume ubthlem.5: |- U e. CBan
  assume ubthlem.6: |- W e. NrmCVec
  assume ubthlem.7: |- ( ph -> T C_ ( U BLnOp W ) )
  assume ubthlem.8: |- ( ph -> A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c )
  assume ubthlem.9: |- A = ( k e. NN |-> { z e. X | A. t e. T ( N ` ( t ` z ) ) <_ k } )
  assume ubthlem.10: |- ( ph -> K e. NN )
  assume ubthlem.11: |- ( ph -> P e. X )
  assume ubthlem.12: |- ( ph -> R e. RR+ )
  assume ubthlem.13: |- ( ph -> { z e. X | ( P D z ) <_ R } C_ ( A ` K ) )

  disjoint c k
  disjoint c x
  disjoint c z
  disjoint A c
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint c t
  disjoint D c
  disjoint k t
  disjoint D k
  disjoint t x
  disjoint t z
  disjoint D t
  disjoint D x
  disjoint D z
  disjoint J k
  disjoint J t
  disjoint J x
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
  disjoint N c
  disjoint N d
  disjoint N k
  disjoint N t
  disjoint N x
  disjoint N z
  disjoint P t
  disjoint P z
  disjoint c ph
  disjoint k ph
  disjoint ph t
  disjoint ph x
  disjoint R d
  disjoint R t
  disjoint R x
  disjoint R z
  disjoint T c
  disjoint T d
  disjoint T k
  disjoint T t
  disjoint T x
  disjoint T z
  disjoint U c
  disjoint U d
  disjoint U t
  disjoint U x
  disjoint U z
  disjoint W c
  disjoint W d
  disjoint W t
  disjoint W x
  disjoint X c
  disjoint X d
  disjoint X k
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint c n
  disjoint c r
  disjoint c y
  disjoint k n
  disjoint k r
  disjoint k y
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
  disjoint y z
  disjoint A y
  disjoint n t
  disjoint D n
  disjoint r t
  disjoint D r
  disjoint J n
  disjoint t y
  disjoint J y
  disjoint c m
  disjoint c u
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d u
  disjoint d y
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
  disjoint N n
  disjoint r u
  disjoint N r
  disjoint t u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint N u
  disjoint N y
  disjoint n ph
  disjoint ph r
  disjoint ph y
  disjoint T m
  disjoint T n
  disjoint T r
  disjoint T u
  disjoint T y
  disjoint U n
  disjoint U r
  disjoint U y
  disjoint W n
  disjoint W r
  disjoint W y
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X y
  assert |- ( ph -> E. d e. RR A. t e. T ( ( U normOpOLD W ) ` t ) <_ d )

  proof
    wph
    cK
    cK
    caddc
    co
    #
    cR
    cdiv
    co
    #
    cr
    wcel
    vt
    cv
    #
    cU
    cW
    cnmoo
    co
    #
    cfv
    #
    @1
    cle
    wbr
    #
    vt
    cT
    wral
    #
    @4
    vd
    cv
    #
    cle
    wbr
    #
    vt
    cT
    wral
    #
    vd
    cr
    wrex
    wph
    @1
    wph
    @0
    cR
    wph
    cK
    cK
    wph
    cK
    ubthlem.10
    nnrpd
    #
    @10
    rpaddcld
    #
    ubthlem.12
    rpdivcld
    #
    rpred
    wph
    @5
    vt
    cT
    wph
    @2
    cT
    wcel
    #
    wa
    #
    @5
    vx
    cv
    #
    cU
    cnmcv
    cfv
    #
    cfv
    #
    c1
    cle
    wbr
    #
    @15
    @2
    cfv
    #
    cN
    cfv
    #
    @1
    cle
    wbr
    #
    wi
    #
    vx
    cX
    wral
    #
    @14
    @22
    vx
    cX
    @14
    @15
    cX
    wcel
    #
    wa
    #
    @18
    cP
    cR
    @15
    cU
    cns
    cfv
    #
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cX
    wcel
    #
    @29
    @2
    cfv
    #
    cN
    cfv
    #
    cK
    cle
    wbr
    #
    vt
    cT
    wral
    #
    wa
    #
    @21
    @25
    cP
    @29
    cD
    co
    #
    cR
    cle
    wbr
    #
    @29
    cK
    cA
    cfv
    #
    wcel
    #
    @18
    @35
    @25
    cP
    vz
    cv
    #
    cD
    co
    #
    cR
    cle
    wbr
    #
    @40
    @38
    wcel
    #
    wi
    #
    vz
    cX
    wral
    #
    @30
    @37
    @39
    wi
    #
    wph
    @45
    @13
    @24
    wph
    @42
    vz
    cX
    crab
    #
    @38
    wss
    @45
    ubthlem.13
    @42
    vz
    cX
    @38
    rabss
    sylib
    ad2antrr
    @25
    cU
    cnv
    wcel
    #
    cP
    cX
    wcel
    #
    @27
    cX
    wcel
    #
    @30
    @48
    @25
    cU
    ccbn
    wcel
    #
    @48
    ubthlem.5
    cU
    bnnv
    ax-mp
    #
    a1i
    #
    wph
    @49
    @13
    @24
    ubthlem.11
    ad2antrr
    #
    @25
    @48
    cR
    cc
    wcel
    #
    @24
    @50
    @53
    @25
    cR
    wph
    cR
    crp
    wcel
    @13
    @24
    ubthlem.12
    ad2antrr
    #
    rpcnd
    #
    @14
    @24
    simpr
    #
    cR
    @15
    @26
    cU
    cX
    ubth.1
    @26
    eqid
    #
    nvscl
    syl3anc
    #
    cP
    @27
    cU
    @28
    cX
    ubth.1
    @28
    eqid
    #
    nvgcl
    syl3anc
    #
    @44
    @46
    vz
    @29
    cX
    @40
    @29
    wceq
    #
    @42
    @37
    @43
    @39
    @63
    @41
    @36
    cR
    cle
    @40
    @29
    cP
    cD
    oveq2
    breq1d
    @40
    @29
    @38
    eleq1
    imbi12d
    rspccv
    sylc
    @25
    @37
    cR
    @17
    cmul
    co
    #
    cR
    c1
    cmul
    co
    #
    cle
    wbr
    @18
    @25
    @36
    @64
    cR
    @65
    cle
    @25
    @36
    @27
    @16
    cfv
    #
    @64
    @25
    @36
    @29
    cP
    cD
    co
    #
    @29
    cP
    cU
    cnsb
    cfv
    #
    co
    #
    @16
    cfv
    #
    @66
    @25
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @49
    @30
    @36
    @67
    wceq
    @71
    @25
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
    @71
    @51
    @72
    ubthlem.5
    cD
    cU
    cX
    ubth.1
    ubthlem.3
    cbncms
    ax-mp
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    mp2b
    #
    a1i
    @54
    @62
    cP
    @29
    cD
    cX
    xmetsym
    syl3anc
    @25
    @48
    @30
    @49
    @67
    @70
    wceq
    @53
    @62
    @54
    @29
    cP
    cD
    cU
    @68
    @16
    cX
    ubth.1
    @68
    eqid
    #
    @16
    eqid
    #
    ubthlem.3
    imsdval
    syl3anc
    @25
    @69
    @27
    @16
    @25
    @48
    @49
    @50
    @69
    @27
    wceq
    @53
    @54
    @60
    cP
    @27
    cU
    @28
    @68
    cX
    ubth.1
    @61
    @74
    nvpncan2
    syl3anc
    #
    fveq2d
    3eqtrd
    @25
    @48
    cR
    cr
    wcel
    cc0
    cR
    cle
    wbr
    wa
    #
    @24
    @66
    @64
    wceq
    @53
    @25
    cR
    @56
    rprege0d
    #
    @58
    cR
    @15
    @26
    cU
    @16
    cX
    ubth.1
    @59
    @75
    nvsge0
    syl3anc
    eqtrd
    @25
    @65
    cR
    @25
    cR
    @57
    mulid1d
    eqcomd
    breq12d
    @25
    @17
    c1
    cR
    @24
    @17
    cr
    wcel
    #
    @14
    @48
    @24
    @79
    @52
    @15
    cU
    @16
    cX
    ubth.1
    @75
    nvcl
    mpan
    adantl
    @25
    1red
    @56
    lemul2d
    bitr4d
    wph
    @39
    @35
    wb
    @13
    @24
    wph
    @39
    @29
    @40
    @2
    cfv
    #
    cN
    cfv
    #
    cK
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
    wcel
    @35
    wph
    @38
    @84
    @29
    wph
    cK
    cn
    wcel
    @38
    @84
    wceq
    ubthlem.10
    vk
    cK
    @81
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
    @84
    cn
    cA
    @85
    cK
    wceq
    #
    @87
    @83
    vz
    cX
    @88
    @86
    @82
    vt
    cT
    @85
    cK
    @81
    cle
    breq2
    ralbidv
    rabbidv
    ubthlem.9
    @83
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
    fvmpt
    syl
    #
    eleq2d
    @83
    @34
    vz
    @29
    cX
    @63
    @82
    @33
    vt
    cT
    @63
    @81
    @32
    cK
    cle
    @63
    @80
    @31
    cN
    @40
    @29
    @2
    fveq2
    fveq2d
    breq1d
    ralbidv
    elrab
    syl6bb
    ad2antrr
    3imtr3d
    @25
    @34
    @21
    @30
    @25
    @34
    @33
    @21
    @13
    @34
    @33
    wi
    wph
    @24
    @34
    @13
    @33
    @33
    vt
    cT
    rsp
    com12
    ad2antlr
    @25
    @33
    cR
    @20
    cmul
    co
    #
    @0
    cle
    wbr
    #
    @21
    @25
    @33
    @32
    cP
    @2
    cfv
    #
    cN
    cfv
    #
    caddc
    co
    #
    @0
    cle
    wbr
    #
    @91
    @25
    @33
    @93
    cK
    cle
    wbr
    #
    @95
    @14
    @96
    @24
    wph
    @96
    vt
    cT
    wph
    @49
    @96
    vt
    cT
    wral
    #
    wph
    cP
    @84
    wcel
    @49
    @97
    wa
    wph
    cP
    @38
    @84
    wph
    @47
    @38
    cP
    ubthlem.13
    wph
    @49
    cP
    cP
    cD
    co
    #
    cR
    cle
    wbr
    #
    cP
    @47
    wcel
    ubthlem.11
    wph
    @98
    cc0
    cR
    cle
    wph
    @71
    @49
    @98
    cc0
    wceq
    @73
    ubthlem.11
    cP
    cD
    cX
    xmet0
    sylancr
    wph
    cR
    ubthlem.12
    rpge0d
    eqbrtrd
    @42
    @99
    vz
    cP
    cX
    @40
    cP
    wceq
    #
    @41
    @98
    cR
    cle
    @40
    cP
    cP
    cD
    oveq2
    breq1d
    elrab
    sylanbrc
    sseldd
    @89
    eleqtrd
    @83
    @97
    vz
    cP
    cX
    @100
    @82
    @96
    vt
    cT
    @100
    @81
    @93
    cK
    cle
    @100
    @80
    @92
    cN
    @40
    cP
    @2
    fveq2
    fveq2d
    breq1d
    ralbidv
    elrab
    sylib
    simprd
    r19.21bi
    adantr
    @25
    @32
    cr
    wcel
    #
    @93
    cr
    wcel
    #
    cK
    cr
    wcel
    #
    @103
    @33
    @96
    wa
    @95
    wi
    @25
    cW
    cnv
    wcel
    #
    @31
    cW
    cba
    cfv
    #
    wcel
    #
    @101
    ubthlem.6
    @25
    cX
    @105
    @29
    @2
    @14
    cX
    @105
    @2
    wf
    #
    @24
    @14
    @107
    @2
    ccnv
    @15
    cima
    cJ
    ccld
    cfv
    wcel
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
    wral
    #
    @14
    @2
    cU
    cW
    cblo
    co
    #
    wcel
    #
    @107
    @110
    wa
    #
    wph
    cT
    @111
    @2
    ubthlem.7
    sselda
    #
    @112
    @2
    cJ
    @109
    ccn
    co
    wcel
    #
    @113
    @111
    cD
    @108
    @2
    cU
    cJ
    @109
    cW
    ubthlem.3
    @108
    eqid
    #
    ubthlem.4
    @109
    eqid
    #
    @111
    eqid
    #
    @52
    ubthlem.6
    blocn2
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @109
    @105
    ctopon
    cfv
    wcel
    #
    @115
    @113
    wb
    @71
    @119
    @73
    cD
    cJ
    cX
    ubthlem.4
    mopntopon
    ax-mp
    @104
    @108
    @105
    cxmt
    cfv
    wcel
    @120
    ubthlem.6
    @108
    cW
    @105
    @105
    eqid
    #
    @116
    imsxmet
    @108
    @109
    @105
    @117
    mopntopon
    mp2b
    vx
    @2
    cJ
    @109
    cX
    @105
    iscncl
    mp2an
    sylib
    syl
    simpld
    #
    adantr
    #
    @62
    ffvelrnd
    #
    @31
    cW
    cN
    @105
    @121
    ubth.2
    nvcl
    sylancr
    #
    @25
    @104
    @92
    @105
    wcel
    #
    @102
    ubthlem.6
    @25
    cX
    @105
    cP
    @2
    @123
    @54
    ffvelrnd
    #
    @92
    cW
    cN
    @105
    @121
    ubth.2
    nvcl
    sylancr
    #
    wph
    @103
    @13
    @24
    wph
    cK
    ubthlem.10
    nnred
    ad2antrr
    #
    @129
    @32
    @93
    cK
    cK
    le2add
    syl22anc
    mpan2d
    @25
    @90
    @94
    cle
    wbr
    #
    @95
    @91
    @25
    @31
    @92
    cW
    cnsb
    cfv
    #
    co
    #
    cN
    cfv
    #
    @90
    @94
    cle
    @25
    @133
    cR
    @19
    cW
    cns
    cfv
    #
    co
    #
    cN
    cfv
    #
    @90
    @25
    @132
    @135
    cN
    @25
    @69
    @2
    cfv
    #
    @27
    @2
    cfv
    #
    @132
    @135
    @25
    @69
    @27
    @2
    @76
    fveq2d
    @25
    @48
    @104
    @2
    cU
    cW
    clno
    co
    #
    wcel
    #
    @30
    @49
    @137
    @132
    wceq
    @53
    @104
    @25
    ubthlem.6
    a1i
    #
    @14
    @140
    @24
    @14
    @112
    @140
    @114
    @48
    @104
    @112
    @140
    @52
    ubthlem.6
    @111
    @2
    cU
    @139
    cW
    @139
    eqid
    #
    @118
    bloln
    mp3an12
    syl
    adantr
    #
    @62
    @54
    @29
    cP
    @2
    cU
    @139
    @68
    @131
    cW
    cX
    ubth.1
    @74
    @131
    eqid
    #
    @142
    lnosub
    syl32anc
    @25
    @48
    @104
    @140
    @55
    @24
    @138
    @135
    wceq
    @53
    @141
    @143
    @57
    @58
    cR
    @15
    @26
    @134
    @2
    cU
    @139
    cW
    cX
    ubth.1
    @59
    @134
    eqid
    #
    @142
    lnomul
    syl32anc
    3eqtr3d
    fveq2d
    @25
    @104
    @77
    @19
    @105
    wcel
    #
    @136
    @90
    wceq
    @141
    @78
    @14
    cX
    @105
    @15
    @2
    @122
    ffvelrnda
    #
    cR
    @19
    @134
    cW
    cN
    @105
    @121
    @145
    ubth.2
    nvsge0
    syl3anc
    eqtrd
    @25
    @104
    @106
    @126
    @133
    @94
    cle
    wbr
    @141
    @124
    @127
    @31
    @92
    cW
    @131
    cN
    @105
    @121
    @144
    ubth.2
    nvmtri
    syl3anc
    eqbrtrrd
    @25
    @90
    cr
    wcel
    @94
    cr
    wcel
    @0
    cr
    wcel
    #
    @130
    @95
    wa
    @91
    wi
    @25
    cR
    @20
    @25
    cR
    @56
    rpred
    @25
    @104
    @146
    @20
    cr
    wcel
    ubthlem.6
    @147
    @19
    cW
    cN
    @105
    @121
    ubth.2
    nvcl
    sylancr
    #
    remulcld
    @25
    @32
    @93
    @125
    @128
    readdcld
    wph
    @148
    @13
    @24
    wph
    @0
    @11
    rpred
    ad2antrr
    #
    @90
    @94
    @0
    letr
    syl3anc
    mpand
    syld
    @25
    @20
    @0
    cR
    @149
    @150
    @56
    lemuldiv2d
    sylibd
    syld
    adantld
    syld
    ralrimiva
    @14
    @107
    @1
    cxr
    wcel
    #
    @5
    @23
    wb
    @122
    wph
    @151
    @13
    wph
    @1
    @12
    rpxrd
    adantr
    vx
    @1
    @2
    cU
    @16
    cN
    @3
    cW
    cX
    @105
    ubth.1
    @121
    @75
    ubth.2
    @3
    eqid
    @52
    ubthlem.6
    nmoubi
    syl2anc
    mpbird
    ralrimiva
    @9
    @6
    vd
    @1
    cr
    @7
    @1
    wceq
    @8
    @5
    vt
    cT
    @7
    @1
    @4
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
end
