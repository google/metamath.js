include "clm.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "wfun.mm"
include "wceq.mm"
include "cxmt.mm"
include "cha.mm"
include "ccphlo.mm"
include "cnv.mm"
include "phnv.mm"
include "imsxmet.mm"
include "3syl.mm"
include "methaus.mm"
include "lmfun.mm"
include "minvecolem4a.mm"
include "crest.mm"
include "c1.mm"
include "cvv.mm"
include "cn.mm"
include "eqid.mm"
include "nnuz.mm"
include "cba.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ctop.mm"
include "syl.mm"
include "mopntop.mm"
include "ctopon.mm"
include "wss.mm"
include "css.mm"
include "ccbn.mm"
include "cin.mm"
include "wa.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "sspba.mm"
include "syl2anc.mm"
include "xmetres2.mm"
include "mopntopon.mm"
include "lmcl.mm"
include "1zzd.mm"
include "lmss.mm"
include "metrest.mm"
include "fveq2d.mm"
include "breqd.mm"
include "bitrd.mm"
include "mpbird.mm"
include "funbrfv.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "minvecolem4b.mm"
include "imsdval.mm"
include "syl3anc.mm"
include "adantr.mm"
include "cr.mm"
include "cme.mm"
include "imsmet.mm"
include "metcl.mm"
include "minvecolem4c.mm"
include "sselda.mm"
include "nvmcl.mm"
include "nvcl.mm"
include "wn.mm"
include "clt.mm"
include "ltnled.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cfl.mm"
include "cuz.mm"
include "cc0.mm"
include "cn0.mm"
include "cexp.mm"
include "cmin.mm"
include "crp.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "resqcld.mm"
include "resubcld.mm"
include "cmul.mm"
include "ltadd1d.mm"
include "recnd.mm"
include "2timesd.mm"
include "breq1d.mm"
include "wb.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltmuldiv2.mm"
include "3bitr2d.mm"
include "cinf.mm"
include "c0.mm"
include "wne.mm"
include "minvecolem1.mm"
include "simp3d.mm"
include "simp1d.mm"
include "simp2d.mm"
include "0re.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "metge0.mm"
include "addge0d.mm"
include "divge0.mm"
include "syl21anc.mm"
include "lt2sqd.mm"
include "posdifd.mm"
include "3bitrd.mm"
include "biimpa.mm"
include "elrpd.mm"
include "rpreccld.mm"
include "syl5eqel.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "nnzd.mm"
include "breqtrrd.mm"
include "rexrd.mm"
include "simpll.mm"
include "eluznn.mm"
include "sylan.mm"
include "fssd.mm"
include "ffvelrnda.mm"
include "ad2antrr.mm"
include "nnrecred.mm"
include "rpred.mm"
include "reflcl.mm"
include "peano2re.mm"
include "nnred.mm"
include "fllep1.mm"
include "eluzle.mm"
include "adantl.mm"
include "letrd.mm"
include "syl5eqbrr.mm"
include "1red.mm"
include "nngt0d.mm"
include "lediv23.mm"
include "syl122anc.mm"
include "mpbid.mm"
include "leaddsub2d.mm"
include "le2sqd.mm"
include "lmle.mm"
include "leadd2d.mm"
include "lemuldiv2.mm"
include "mp3an3.mm"
include "biimpar.mm"
include "syldan.mm"
include "ex.mm"
include "sylbird.mm"
include "pm2.18d.mm"
include "cmpt.mm"
include "crn.mm"
include "simpr.mm"
include "elrnmpt1.mm"
include "sylancl.mm"
include "syl6eleqr.mm"
include "infrelb.mm"
include "syl5eqbr.mm"
include "eqbrtrrd.mm"
include "ralrimiva.mm"
include "oveq2.mm"

theorem minvecolem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let cK: class K
  let cL: class L
  let vf: setvar f
  assume minveco.x: |- X = ( BaseSet ` U )
  assume minveco.m: |- M = ( -v ` U )
  assume minveco.n: |- N = ( normCV ` U )
  assume minveco.y: |- Y = ( BaseSet ` W )
  assume minveco.u: |- ( ph -> U e. CPreHilOLD )
  assume minveco.w: |- ( ph -> W e. ( ( SubSp ` U ) i^i CBan ) )
  assume minveco.a: |- ( ph -> A e. X )
  assume minveco.d: |- D = ( IndMet ` U )
  assume minveco.j: |- J = ( MetOpen ` D )
  assume minveco.r: |- R = ran ( y e. Y |-> ( N ` ( A M y ) ) )
  assume minveco.s: |- S = inf ( R , RR , < )
  assume minveco.f: |- ( ph -> F : NN --> Y )
  assume minveco.1: |- ( ( ph /\ n e. NN ) -> ( ( A D ( F ` n ) ) ^ 2 ) <_ ( ( S ^ 2 ) + ( 1 / n ) ) )
  assume minveco.t: |- T = ( 1 / ( ( ( ( ( A D ( ( ~~>t ` J ) ` F ) ) + S ) / 2 ) ^ 2 ) - ( S ^ 2 ) ) )

  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint U x
  disjoint U y
  disjoint W x
  disjoint W y
  disjoint T n
  disjoint X n
  disjoint X x
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint K y
  disjoint L y
  disjoint f j
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint M f
  disjoint j w
  disjoint M j
  disjoint M w
  disjoint N f
  disjoint N j
  disjoint N w
  disjoint f k
  disjoint f n
  disjoint f ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint ph w
  disjoint R w
  disjoint S f
  disjoint S k
  disjoint S w
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A w
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D w
  disjoint U w
  disjoint W w
  disjoint X j
  disjoint X k
  disjoint X w
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y w
  assert |- ( ph -> E. x e. Y A. y e. Y ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) )

  proof
    wph
    cF
    cJ
    clm
    cfv
    #
    cfv
    #
    cY
    wcel
    cA
    @1
    cM
    co
    #
    cN
    cfv
    #
    cA
    vy
    cv
    #
    cM
    co
    #
    cN
    cfv
    #
    cle
    wbr
    #
    vy
    cY
    wral
    #
    cA
    vx
    cv
    #
    cM
    co
    #
    cN
    cfv
    #
    @6
    cle
    wbr
    #
    vy
    cY
    wral
    #
    vx
    cY
    wrex
    wph
    @1
    cF
    cD
    cY
    cY
    cxp
    cres
    #
    cmopn
    cfv
    #
    clm
    cfv
    #
    cfv
    #
    cY
    wph
    @0
    wfun
    #
    cF
    @17
    @0
    wbr
    #
    @1
    @17
    wceq
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    cha
    wcel
    @18
    wph
    cU
    ccphlo
    wcel
    #
    cU
    cnv
    wcel
    #
    @20
    minveco.u
    cU
    phnv
    #
    cD
    cU
    cX
    minveco.x
    minveco.d
    imsxmet
    #
    3syl
    #
    cD
    cJ
    cX
    minveco.j
    methaus
    cJ
    lmfun
    3syl
    wph
    @19
    cF
    @17
    @16
    wbr
    #
    wph
    vy
    cA
    cD
    cR
    cS
    cU
    vn
    cF
    cJ
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    minveco.u
    minveco.w
    minveco.a
    minveco.d
    minveco.j
    minveco.r
    minveco.s
    minveco.f
    minveco.1
    minvecolem4a
    #
    wph
    @19
    cF
    @17
    cJ
    cY
    crest
    co
    #
    clm
    cfv
    #
    wbr
    @26
    wph
    @17
    cF
    cJ
    @28
    c1
    cvv
    cY
    cn
    @28
    eqid
    nnuz
    cY
    cvv
    wcel
    wph
    cY
    cW
    cba
    cfv
    cvv
    minveco.y
    cW
    cba
    fvex
    eqeltri
    a1i
    wph
    @22
    @20
    cJ
    ctop
    wcel
    wph
    @21
    @22
    minveco.u
    @23
    syl
    #
    @24
    cD
    cJ
    cX
    minveco.j
    mopntop
    3syl
    wph
    @15
    cY
    ctopon
    cfv
    wcel
    #
    @26
    @17
    cY
    wcel
    wph
    @14
    cY
    cxmt
    cfv
    wcel
    #
    @31
    wph
    @20
    cY
    cX
    wss
    #
    @32
    @25
    wph
    @22
    cW
    cU
    css
    cfv
    #
    wcel
    #
    @33
    @30
    wph
    @35
    cW
    ccbn
    wcel
    #
    wph
    cW
    @34
    ccbn
    cin
    wcel
    @35
    @36
    wa
    minveco.w
    cW
    @34
    ccbn
    elin
    sylib
    simpld
    cU
    @34
    cW
    cX
    cY
    minveco.x
    minveco.y
    @34
    eqid
    sspba
    syl2anc
    #
    cD
    cY
    cX
    xmetres2
    syl2anc
    @14
    @15
    cY
    @15
    eqid
    #
    mopntopon
    syl
    @27
    @17
    cF
    @15
    cY
    lmcl
    syl2anc
    #
    wph
    1zzd
    minveco.f
    lmss
    wph
    @29
    @16
    cF
    @17
    wph
    @28
    @15
    clm
    wph
    @20
    @33
    @28
    @15
    wceq
    @25
    @37
    cD
    @14
    cJ
    @15
    cX
    cY
    @14
    eqid
    minveco.j
    @38
    metrest
    syl2anc
    fveq2d
    breqd
    bitrd
    mpbird
    #
    cF
    @17
    @0
    funbrfv
    sylc
    #
    @39
    eqeltrd
    wph
    @7
    vy
    cY
    wph
    @4
    cY
    wcel
    #
    wa
    #
    cA
    @1
    cD
    co
    #
    @3
    @6
    cle
    wph
    @44
    @3
    wceq
    #
    @42
    wph
    @22
    cA
    cX
    wcel
    #
    @1
    cX
    wcel
    #
    @45
    @30
    minveco.a
    wph
    vy
    cA
    cD
    cR
    cS
    cU
    vn
    cF
    cJ
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    minveco.u
    minveco.w
    minveco.a
    minveco.d
    minveco.j
    minveco.r
    minveco.s
    minveco.f
    minveco.1
    minvecolem4b
    #
    cA
    @1
    cD
    cU
    cM
    cN
    cX
    minveco.x
    minveco.m
    minveco.n
    minveco.d
    imsdval
    syl3anc
    adantr
    @43
    @44
    cS
    @6
    wph
    @44
    cr
    wcel
    #
    @42
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @46
    @47
    @49
    wph
    @21
    @22
    @50
    minveco.u
    @23
    cD
    cU
    cX
    minveco.x
    minveco.d
    imsmet
    3syl
    #
    minveco.a
    @48
    cA
    @1
    cD
    cX
    metcl
    syl3anc
    #
    adantr
    wph
    cS
    cr
    wcel
    #
    @42
    wph
    vy
    cA
    cD
    cR
    cS
    cU
    vn
    cF
    cJ
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    minveco.u
    minveco.w
    minveco.a
    minveco.d
    minveco.j
    minveco.r
    minveco.s
    minveco.f
    minveco.1
    minvecolem4c
    #
    adantr
    @43
    @22
    @5
    cX
    wcel
    #
    @6
    cr
    wcel
    wph
    @22
    @42
    @30
    adantr
    #
    @43
    @22
    @46
    @4
    cX
    wcel
    @55
    @56
    wph
    @46
    @42
    minveco.a
    adantr
    wph
    cY
    cX
    @4
    @37
    sselda
    cA
    @4
    cU
    cM
    cX
    minveco.x
    minveco.m
    nvmcl
    syl3anc
    @5
    cU
    cN
    cX
    minveco.x
    minveco.n
    nvcl
    syl2anc
    wph
    @44
    cS
    cle
    wbr
    #
    @42
    wph
    @57
    wph
    @57
    wn
    cS
    @44
    clt
    wbr
    #
    @57
    wph
    cS
    @44
    @54
    @52
    ltnled
    wph
    @58
    @57
    wph
    @58
    @44
    @44
    cS
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    @57
    wph
    @58
    wa
    #
    cD
    @1
    cA
    @60
    vn
    cF
    cJ
    cT
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cX
    @64
    cuz
    cfv
    #
    @65
    eqid
    minveco.j
    wph
    @20
    @58
    @25
    adantr
    @62
    @64
    @62
    cT
    cr
    wcel
    #
    cc0
    cT
    cle
    wbr
    wa
    @63
    cn0
    wcel
    @64
    cn
    wcel
    #
    @62
    cT
    @62
    cT
    c1
    @60
    c2
    cexp
    co
    #
    cS
    c2
    cexp
    co
    #
    cmin
    co
    #
    cdiv
    co
    #
    crp
    minveco.t
    @62
    @70
    @62
    @70
    wph
    @70
    cr
    wcel
    #
    @58
    wph
    @68
    @69
    wph
    @60
    wph
    @59
    wph
    @44
    cS
    @52
    @54
    readdcld
    #
    rehalfcld
    #
    resqcld
    #
    wph
    cS
    @54
    resqcld
    #
    resubcld
    #
    adantr
    wph
    @58
    cc0
    @70
    clt
    wbr
    #
    wph
    @58
    cS
    @60
    clt
    wbr
    #
    @69
    @68
    clt
    wbr
    @78
    wph
    @58
    cS
    cS
    caddc
    co
    #
    @59
    clt
    wbr
    c2
    cS
    cmul
    co
    #
    @59
    clt
    wbr
    #
    @79
    wph
    cS
    @44
    cS
    @54
    @52
    @54
    ltadd1d
    wph
    @81
    @80
    @59
    clt
    wph
    cS
    wph
    cS
    @54
    recnd
    2timesd
    breq1d
    wph
    @53
    @59
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @82
    @79
    wb
    @54
    @73
    @86
    wph
    @84
    @85
    2re
    2pos
    pm3.2i
    #
    a1i
    #
    cS
    @59
    c2
    ltmuldiv2
    syl3anc
    3bitr2d
    wph
    cS
    @60
    @54
    @74
    wph
    cc0
    cR
    cr
    clt
    cinf
    #
    cS
    cle
    wph
    cc0
    @89
    cle
    wbr
    #
    cc0
    vw
    cv
    #
    cle
    wbr
    #
    vw
    cR
    wral
    #
    wph
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    @93
    wph
    vy
    vw
    cA
    cD
    cR
    cU
    cJ
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    minveco.u
    minveco.w
    minveco.a
    minveco.d
    minveco.j
    minveco.r
    minvecolem1
    #
    simp3d
    #
    wph
    @94
    @95
    @9
    @91
    cle
    wbr
    #
    vw
    cR
    wral
    #
    vx
    cr
    wrex
    #
    cc0
    cr
    wcel
    #
    @90
    @93
    wb
    wph
    @94
    @95
    @93
    @96
    simp1d
    #
    wph
    @94
    @95
    @93
    @96
    simp2d
    wph
    @101
    @93
    @100
    0re
    @97
    @99
    @93
    vx
    cc0
    cr
    @9
    cc0
    wceq
    @98
    @92
    vw
    cR
    @9
    cc0
    @91
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    #
    @101
    wph
    0re
    a1i
    vx
    vw
    vw
    cR
    cc0
    infregelb
    syl31anc
    mpbird
    minveco.s
    syl6breqr
    #
    wph
    @83
    cc0
    @59
    cle
    wbr
    @86
    cc0
    @60
    cle
    wbr
    #
    @73
    wph
    @44
    cS
    @52
    @54
    wph
    @50
    @46
    @47
    cc0
    @44
    cle
    wbr
    @51
    minveco.a
    @48
    cA
    @1
    cD
    cX
    metge0
    syl3anc
    @104
    addge0d
    @88
    @59
    c2
    divge0
    syl21anc
    #
    lt2sqd
    wph
    @69
    @68
    @76
    @75
    posdifd
    3bitrd
    biimpa
    #
    elrpd
    rpreccld
    syl5eqel
    #
    rprege0d
    cT
    flge0nn0
    @63
    nn0p1nn
    3syl
    #
    nnzd
    wph
    cF
    @1
    @0
    wbr
    @58
    wph
    cF
    @17
    @1
    @0
    @40
    @41
    breqtrrd
    adantr
    wph
    @46
    @58
    minveco.a
    adantr
    @62
    @60
    wph
    @60
    cr
    wcel
    #
    @58
    @74
    adantr
    rexrd
    @62
    vn
    cv
    #
    @65
    wcel
    #
    wa
    #
    cA
    @111
    cF
    cfv
    #
    cD
    co
    #
    @60
    cle
    wbr
    @115
    c2
    cexp
    co
    #
    @68
    cle
    wbr
    @113
    @116
    @69
    c1
    @111
    cdiv
    co
    #
    caddc
    co
    #
    @68
    @113
    @115
    @113
    wph
    @111
    cn
    wcel
    #
    @115
    cr
    wcel
    #
    wph
    @58
    @112
    simpll
    #
    @62
    @67
    @112
    @119
    @109
    @111
    @64
    eluznn
    sylan
    #
    wph
    @119
    wa
    #
    @50
    @46
    @114
    cX
    wcel
    #
    @120
    wph
    @50
    @119
    @51
    adantr
    #
    wph
    @46
    @119
    minveco.a
    adantr
    #
    wph
    cn
    cX
    @111
    cF
    wph
    cn
    cY
    cX
    cF
    minveco.f
    @37
    fssd
    ffvelrnda
    #
    cA
    @114
    cD
    cX
    metcl
    syl3anc
    syl2anc
    #
    resqcld
    @113
    @69
    @117
    @113
    cS
    wph
    @53
    @58
    @112
    @54
    ad2antrr
    resqcld
    #
    @113
    @111
    @122
    nnrecred
    #
    readdcld
    wph
    @68
    cr
    wcel
    @58
    @112
    @75
    ad2antrr
    #
    @113
    wph
    @119
    @116
    @118
    cle
    wbr
    @121
    @122
    minveco.1
    syl2anc
    @113
    @118
    @68
    cle
    wbr
    @117
    @70
    cle
    wbr
    #
    @113
    @71
    @111
    cle
    wbr
    #
    @132
    @113
    @71
    cT
    @111
    cle
    minveco.t
    @113
    cT
    @64
    @111
    @113
    cT
    @62
    cT
    crp
    wcel
    @112
    @108
    adantr
    rpred
    #
    @113
    @66
    @63
    cr
    wcel
    @64
    cr
    wcel
    @134
    cT
    reflcl
    @63
    peano2re
    3syl
    @113
    @111
    @122
    nnred
    #
    @113
    @66
    cT
    @64
    cle
    wbr
    @134
    cT
    fllep1
    syl
    @112
    @64
    @111
    cle
    wbr
    @62
    @64
    @111
    eluzle
    adantl
    letrd
    syl5eqbrr
    @113
    c1
    cr
    wcel
    @72
    @78
    @111
    cr
    wcel
    cc0
    @111
    clt
    wbr
    @133
    @132
    wb
    @113
    1red
    wph
    @72
    @58
    @112
    @77
    ad2antrr
    @62
    @78
    @112
    @107
    adantr
    @135
    @113
    @111
    @122
    nngt0d
    c1
    @70
    @111
    lediv23
    syl122anc
    mpbid
    @113
    @69
    @117
    @68
    @129
    @130
    @131
    leaddsub2d
    mpbird
    letrd
    @113
    @115
    @60
    @128
    wph
    @110
    @58
    @112
    @74
    ad2antrr
    @113
    wph
    @119
    cc0
    @115
    cle
    wbr
    #
    @121
    @122
    @123
    @50
    @46
    @124
    @136
    @125
    @126
    @127
    cA
    @114
    cD
    cX
    metge0
    syl3anc
    syl2anc
    wph
    @105
    @58
    @112
    @106
    ad2antrr
    le2sqd
    mpbird
    lmle
    wph
    @57
    @61
    wph
    @57
    @44
    @44
    caddc
    co
    #
    @59
    cle
    wbr
    c2
    @44
    cmul
    co
    #
    @59
    cle
    wbr
    #
    @61
    wph
    @44
    cS
    @44
    @52
    @54
    @52
    leadd2d
    wph
    @138
    @137
    @59
    cle
    wph
    @44
    wph
    @44
    @52
    recnd
    2timesd
    breq1d
    wph
    @49
    @83
    @139
    @61
    wb
    #
    @52
    @73
    @49
    @83
    @86
    @140
    @87
    @44
    @59
    c2
    lemuldiv2
    mp3an3
    syl2anc
    3bitr2d
    biimpar
    syldan
    ex
    sylbird
    pm2.18d
    adantr
    @43
    cS
    @89
    @6
    cle
    minveco.s
    @43
    @94
    @100
    @6
    cR
    wcel
    @89
    @6
    cle
    wbr
    wph
    @94
    @42
    @102
    adantr
    wph
    @100
    @42
    @103
    adantr
    @43
    @6
    vy
    cY
    @6
    cmpt
    #
    crn
    #
    cR
    @43
    @42
    @6
    cvv
    wcel
    @6
    @142
    wcel
    wph
    @42
    simpr
    @5
    cN
    fvex
    vy
    cY
    @6
    @141
    cvv
    @141
    eqid
    elrnmpt1
    sylancl
    minveco.r
    syl6eleqr
    vx
    vw
    @6
    cR
    infrelb
    syl3anc
    syl5eqbr
    letrd
    eqbrtrrd
    ralrimiva
    @13
    @8
    vx
    @1
    cY
    @9
    @1
    wceq
    #
    @12
    @7
    vy
    cY
    @143
    @11
    @3
    @6
    cle
    @143
    @10
    @2
    cN
    @9
    @1
    cA
    cM
    oveq2
    fveq2d
    breq1d
    ralbidv
    rspcev
    syl2anc
end
