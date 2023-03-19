include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cnmoo.mm"
include "co.mm"
include "wceq.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "cbvrexv.mm"
include "fveq2.mm"
include "rexralbidv.mm"
include "wa.mm"
include "crab.mm"
include "cn.mm"
include "cmpt.mm"
include "wss.mm"
include "crp.mm"
include "cblo.mm"
include "adantr.mm"
include "simpr.mm"
include "sylib.mm"
include "cbvrabv.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "ubthlem1.mm"
include "wcel.mm"
include "ad3antrrr.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "simprr.mm"
include "ubthlem2.mm"
include "expr.mm"
include "rexlimdva.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "ex.mm"
include "syl5bir.mm"
include "cnmcv.mm"
include "cmul.mm"
include "cnv.mm"
include "ccbn.mm"
include "bnnv.mm"
include "ax-mp.mm"
include "eqid.mm"
include "nvcl.mm"
include "mpan.mm"
include "remulcl.mm"
include "syl2an.mm"
include "cba.mm"
include "wf.mm"
include "sselda.mm"
include "adantlr.mm"
include "ad2ant2r.mm"
include "blof.mm"
include "mp3an12.mm"
include "syl.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "cxr.mm"
include "cmnf.mm"
include "clt.mm"
include "nmoxr.mm"
include "simpllr.mm"
include "nmogtmnf.mm"
include "xrre.mm"
include "syl22anc.mm"
include "ad2antlr.mm"
include "syl2anc.mm"
include "nmblolbi.mm"
include "cc0.mm"
include "nvge0.mm"
include "jca.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "letrd.mm"
include "ralimdva.mm"
include "rspcev.mm"
include "syl6an.mm"
include "ralrimdva.mm"
include "impbid.mm"

theorem ubthlem3
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cD: class D
  let cT: class T
  let cU: class U
  let cJ: class J
  let cN: class N
  let cW: class W
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cA: class A
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

  disjoint d ph
  disjoint c x
  disjoint c t
  disjoint D c
  disjoint t x
  disjoint D t
  disjoint D x
  disjoint J t
  disjoint J x
  disjoint d t
  disjoint d x
  disjoint c d
  disjoint N c
  disjoint N d
  disjoint N t
  disjoint N x
  disjoint c ph
  disjoint ph t
  disjoint ph x
  disjoint T c
  disjoint T d
  disjoint T t
  disjoint T x
  disjoint U c
  disjoint U d
  disjoint U t
  disjoint U x
  disjoint W c
  disjoint W d
  disjoint W t
  disjoint W x
  disjoint X c
  disjoint X d
  disjoint X t
  disjoint X x
  disjoint c k
  disjoint c n
  disjoint c r
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
  disjoint k t
  disjoint D k
  disjoint n t
  disjoint D n
  disjoint r t
  disjoint D r
  disjoint t z
  disjoint D z
  disjoint J k
  disjoint J n
  disjoint t y
  disjoint J y
  disjoint d k
  disjoint d z
  disjoint K d
  disjoint K k
  disjoint K t
  disjoint K x
  disjoint K z
  disjoint c m
  disjoint c u
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d u
  disjoint d y
  disjoint k m
  disjoint k u
  disjoint N k
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
  disjoint N z
  disjoint P t
  disjoint P z
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph y
  disjoint R d
  disjoint R t
  disjoint R x
  disjoint R z
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T r
  disjoint T u
  disjoint T y
  disjoint T z
  disjoint U n
  disjoint U r
  disjoint U y
  disjoint U z
  disjoint W n
  disjoint W r
  disjoint W y
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c <-> E. d e. RR A. t e. T ( ( U normOpOLD W ) ` t ) <_ d ) )

  proof
    wph
    vx
    cv
    #
    vt
    cv
    #
    cfv
    #
    cN
    cfv
    #
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
    #
    @1
    cU
    cW
    cnmoo
    co
    #
    cfv
    #
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
    #
    @8
    vz
    cv
    #
    vu
    cv
    #
    cfv
    #
    cN
    cfv
    #
    @11
    cle
    wbr
    #
    vu
    cT
    wral
    #
    vd
    cr
    wrex
    #
    vz
    cX
    wral
    #
    wph
    @14
    @21
    @7
    vz
    vx
    cX
    @21
    @15
    @1
    cfv
    #
    cN
    cfv
    #
    @4
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
    @15
    @0
    wceq
    #
    @7
    @20
    @26
    vd
    vc
    cr
    @20
    @24
    @11
    cle
    wbr
    #
    vt
    cT
    wral
    @11
    @4
    wceq
    #
    @26
    @19
    @28
    vu
    vt
    cT
    @16
    @1
    wceq
    #
    @18
    @24
    @11
    cle
    @30
    @17
    @23
    cN
    @15
    @16
    @1
    fveq1
    fveq2d
    breq1d
    cbvralv
    @29
    @28
    @25
    vt
    cT
    @11
    @4
    @24
    cle
    breq2
    ralbidv
    syl5bb
    cbvrexv
    @27
    @25
    @5
    vc
    vt
    cr
    cT
    @27
    @24
    @3
    @4
    cle
    @27
    @23
    @2
    cN
    @15
    @0
    @1
    fveq2
    fveq2d
    breq1d
    rexralbidv
    syl5bb
    cbvralv
    #
    wph
    @22
    @14
    wph
    @22
    wa
    #
    vy
    cv
    #
    @15
    cD
    co
    vr
    cv
    #
    cle
    wbr
    vz
    cX
    crab
    vn
    cv
    #
    vm
    cn
    @11
    @16
    cfv
    #
    cN
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    vu
    cT
    wral
    #
    vd
    cX
    crab
    #
    cmpt
    #
    cfv
    wss
    #
    vr
    crp
    wrex
    #
    vy
    cX
    wrex
    vn
    cn
    wrex
    @14
    @32
    vx
    vy
    vz
    vt
    @42
    cD
    cT
    cU
    vk
    vn
    cJ
    cN
    cW
    cX
    vr
    vc
    ubth.1
    ubth.2
    ubthlem.3
    ubthlem.4
    ubthlem.5
    ubthlem.6
    wph
    cT
    cU
    cW
    cblo
    co
    #
    wss
    #
    @22
    ubthlem.7
    adantr
    @32
    @22
    @8
    wph
    @22
    simpr
    @31
    sylib
    #
    vm
    vk
    cn
    @41
    @24
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
    @38
    @48
    wceq
    #
    @41
    @24
    @38
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
    @51
    @40
    @54
    vd
    vz
    cX
    @40
    @11
    @1
    cfv
    #
    cN
    cfv
    #
    @38
    cle
    wbr
    #
    vt
    cT
    wral
    @11
    @15
    wceq
    #
    @54
    @39
    @57
    vu
    vt
    cT
    @30
    @37
    @56
    @38
    cle
    @30
    @36
    @55
    cN
    @11
    @16
    @1
    fveq1
    fveq2d
    breq1d
    cbvralv
    @58
    @57
    @53
    vt
    cT
    @58
    @56
    @24
    @38
    cle
    @58
    @55
    @23
    cN
    @11
    @15
    @1
    fveq2
    fveq2d
    breq1d
    ralbidv
    syl5bb
    cbvrabv
    @52
    @54
    @50
    vz
    cX
    @52
    @53
    @49
    vt
    cT
    @38
    @48
    @24
    cle
    breq2
    ralbidv
    rabbidv
    syl5eq
    cbvmptv
    #
    ubthlem1
    @32
    @44
    @14
    vn
    vy
    cn
    cX
    @32
    @35
    cn
    wcel
    #
    @33
    cX
    wcel
    #
    wa
    #
    wa
    #
    @43
    @14
    vr
    crp
    @63
    @34
    crp
    wcel
    #
    @43
    @14
    @63
    @64
    @43
    wa
    #
    wa
    vx
    vz
    vt
    @42
    cD
    @33
    @34
    cT
    cU
    vk
    cJ
    @35
    cN
    cW
    cX
    vc
    vd
    ubth.1
    ubth.2
    ubthlem.3
    ubthlem.4
    ubthlem.5
    ubthlem.6
    wph
    @46
    @22
    @62
    @65
    ubthlem.7
    ad3antrrr
    @32
    @8
    @62
    @65
    @47
    ad2antrr
    @59
    @32
    @60
    @61
    @65
    simplrl
    @32
    @60
    @61
    @65
    simplrr
    @63
    @64
    @43
    simprl
    @63
    @64
    @43
    simprr
    ubthlem2
    expr
    rexlimdva
    rexlimdvva
    mpd
    ex
    syl5bir
    wph
    @13
    @8
    vd
    cr
    wph
    @11
    cr
    wcel
    #
    wa
    #
    @13
    @7
    vx
    cX
    @67
    @0
    cX
    wcel
    #
    wa
    #
    @11
    @0
    cU
    cnmcv
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cr
    wcel
    #
    @13
    @3
    @72
    cle
    wbr
    #
    vt
    cT
    wral
    #
    @7
    @67
    @66
    @71
    cr
    wcel
    #
    @73
    @68
    wph
    @66
    simpr
    cU
    cnv
    wcel
    #
    @68
    @76
    cU
    ccbn
    wcel
    @77
    ubthlem.5
    cU
    bnnv
    ax-mp
    #
    @0
    cU
    @70
    cX
    ubth.1
    @70
    eqid
    #
    nvcl
    mpan
    #
    @11
    @71
    remulcl
    syl2an
    #
    @69
    @12
    @74
    vt
    cT
    @69
    @1
    cT
    wcel
    #
    @12
    @74
    @69
    @82
    @12
    wa
    #
    wa
    #
    @3
    @10
    @71
    cmul
    co
    #
    @72
    @84
    @2
    cW
    cba
    cfv
    #
    wcel
    #
    @3
    cr
    wcel
    #
    @84
    cX
    @86
    @0
    @1
    @84
    @1
    @45
    wcel
    #
    cX
    @86
    @1
    wf
    #
    @67
    @82
    @89
    @68
    @12
    wph
    @82
    @89
    @66
    wph
    cT
    @45
    @1
    ubthlem.7
    sselda
    adantlr
    ad2ant2r
    #
    @77
    cW
    cnv
    wcel
    #
    @89
    @90
    @78
    ubthlem.6
    @45
    @1
    cU
    cW
    cX
    @86
    ubth.1
    @86
    eqid
    #
    @45
    eqid
    #
    blof
    mp3an12
    syl
    #
    @67
    @68
    @83
    simplr
    #
    ffvelrnd
    @92
    @87
    @88
    ubthlem.6
    @2
    cW
    cN
    @86
    @93
    ubth.2
    nvcl
    mpan
    syl
    @84
    @10
    cr
    wcel
    #
    @76
    @85
    cr
    wcel
    @84
    @10
    cxr
    wcel
    #
    @66
    cmnf
    @10
    clt
    wbr
    #
    @12
    @97
    @84
    @90
    @98
    @95
    @77
    @92
    @90
    @98
    @78
    ubthlem.6
    @1
    cU
    @9
    cW
    cX
    @86
    ubth.1
    @93
    @9
    eqid
    #
    nmoxr
    mp3an12
    syl
    wph
    @66
    @68
    @83
    simpllr
    #
    @84
    @90
    @99
    @95
    @77
    @92
    @90
    @99
    @78
    ubthlem.6
    @1
    cU
    @9
    cW
    cX
    @86
    ubth.1
    @93
    @100
    nmogtmnf
    mp3an12
    syl
    @69
    @82
    @12
    simprr
    #
    @10
    @11
    xrre
    syl22anc
    #
    @68
    @76
    @67
    @83
    @80
    ad2antlr
    @10
    @71
    remulcl
    syl2anc
    @69
    @73
    @83
    @81
    adantr
    @84
    @89
    @68
    @3
    @85
    cle
    wbr
    @91
    @96
    @0
    @45
    @1
    cU
    @70
    cN
    @9
    cW
    cX
    ubth.1
    @79
    ubth.2
    @100
    @94
    @78
    ubthlem.6
    nmblolbi
    syl2anc
    @84
    @97
    @66
    @76
    cc0
    @71
    cle
    wbr
    #
    wa
    #
    @12
    @85
    @72
    cle
    wbr
    @103
    @101
    @68
    @105
    @67
    @83
    @68
    @76
    @104
    @80
    @77
    @68
    @104
    @78
    @0
    cU
    @70
    cX
    ubth.1
    @79
    nvge0
    mpan
    jca
    ad2antlr
    @102
    @10
    @11
    @71
    lemul1a
    syl31anc
    letrd
    expr
    ralimdva
    @6
    @75
    vc
    @72
    cr
    @4
    @72
    wceq
    @5
    @74
    vt
    cT
    @4
    @72
    @3
    cle
    breq2
    ralbidv
    rspcev
    syl6an
    ralrimdva
    rexlimdva
    impbid
end
