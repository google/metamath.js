include "co.mm"
include "c2.mm"
include "cexp.mm"
include "c4.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "c1.mm"
include "cdiv.mm"
include "cpv.mm"
include "cfv.mm"
include "cns.mm"
include "cr.mm"
include "wcel.mm"
include "4re.mm"
include "clt.mm"
include "cinf.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "cc0.mm"
include "minvecolem1.mm"
include "simp1d.mm"
include "simp2d.mm"
include "0re.mm"
include "simp3d.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "infrecl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "resqcld.mm"
include "remulcl.mm"
include "cme.mm"
include "cnv.mm"
include "ccphlo.mm"
include "phnv.mm"
include "syl.mm"
include "imsmet.mm"
include "css.mm"
include "ccbn.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "eqid.mm"
include "sspba.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "metcl.mm"
include "readdcld.mm"
include "cc.mm"
include "ax-1cn.mm"
include "halfcl.mm"
include "mp1i.mm"
include "sspgval.mm"
include "syl22anc.mm"
include "sspnv.mm"
include "nvgcl.mm"
include "eqeltrrd.mm"
include "sspsval.mm"
include "nvscl.mm"
include "nvmcl.mm"
include "nvcl.mm"
include "wb.mm"
include "a1i.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "syl6breqr.mm"
include "cmpt.mm"
include "crn.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "sylancl.mm"
include "fvex.mm"
include "elrnmpti.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "infrelb.mm"
include "syl5eqbr.mm"
include "le2sq2.mm"
include "wa.mm"
include "4pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "mp3an3.mm"
include "mpbid.mm"
include "leadd1dd.mm"
include "le2addd.mm"
include "recnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "2re.mm"
include "2pos.mm"
include "phpar2.mm"
include "2cn.mm"
include "sqmul.mm"
include "sq2.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "cabs.mm"
include "nvs.mm"
include "0le2.mm"
include "absid.mm"
include "mp2an.mm"
include "nvmdi.mm"
include "syl13anc.mm"
include "nv2.mm"
include "2ne0.mm"
include "recidi.mm"
include "nvsid.mm"
include "syl5eq.mm"
include "nvsass.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "nvaddsub4.mm"
include "syl122anc.mm"
include "3eqtr2d.mm"
include "oveq1d.mm"
include "imsdval.mm"
include "metsym.mm"
include "nvnnncan1.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "2t2e4.mm"
include "mulassd.mm"
include "syl5eqr.mm"
include "3brtr4d.mm"
include "letrd.mm"
include "4cn.mm"
include "adddid.mm"
include "breqtrd.mm"
include "leadd2d.mm"

theorem minvecolem2
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let cF: class F
  let vk: setvar k
  let vw: setvar w
  let vf: setvar f
  let cT: class T
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
  assume minvecolem2.1: |- ( ph -> B e. RR )
  assume minvecolem2.2: |- ( ph -> 0 <_ B )
  assume minvecolem2.3: |- ( ph -> K e. Y )
  assume minvecolem2.4: |- ( ph -> L e. Y )
  assume minvecolem2.5: |- ( ph -> ( ( A D K ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) )
  assume minvecolem2.6: |- ( ph -> ( ( A D L ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) )

  disjoint J y
  disjoint K y
  disjoint L y
  disjoint M y
  disjoint N y
  disjoint ph y
  disjoint S y
  disjoint A y
  disjoint D y
  disjoint U y
  disjoint W y
  disjoint Y y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint n w
  disjoint J n
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint J x
  disjoint f j
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint M f
  disjoint j w
  disjoint M j
  disjoint M w
  disjoint M x
  disjoint N f
  disjoint N j
  disjoint N w
  disjoint N x
  disjoint f k
  disjoint f n
  disjoint f ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph w
  disjoint ph x
  disjoint R w
  disjoint R x
  disjoint S f
  disjoint S k
  disjoint S n
  disjoint S w
  disjoint S x
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A n
  disjoint A w
  disjoint A x
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D w
  disjoint D x
  disjoint U w
  disjoint U x
  disjoint W w
  disjoint W x
  disjoint T n
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y n
  disjoint Y w
  disjoint Y x
  assert |- ( ph -> ( ( K D L ) ^ 2 ) <_ ( 4 x. B ) )

  proof
    wph
    cK
    cL
    cD
    co
    #
    c2
    cexp
    co
    #
    c4
    cB
    cmul
    co
    #
    cle
    wbr
    c4
    cS
    c2
    cexp
    co
    #
    cmul
    co
    #
    @1
    caddc
    co
    #
    @4
    @2
    caddc
    co
    #
    cle
    wbr
    wph
    @5
    c4
    @3
    cB
    caddc
    co
    #
    cmul
    co
    #
    @6
    cle
    wph
    @5
    c4
    cA
    c1
    c2
    cdiv
    co
    #
    cK
    cL
    cU
    cpv
    cfv
    #
    co
    #
    cU
    cns
    cfv
    #
    co
    #
    cM
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    @1
    caddc
    co
    #
    @8
    wph
    @4
    @1
    wph
    c4
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    4re
    wph
    cS
    wph
    cS
    cR
    cr
    clt
    cinf
    #
    cr
    minveco.s
    wph
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    vx
    cv
    #
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
    vx
    cr
    wrex
    #
    @21
    cr
    wcel
    wph
    @22
    @23
    cc0
    @25
    cle
    wbr
    #
    vw
    cR
    wral
    #
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
    simp1d
    #
    wph
    @22
    @23
    @30
    @31
    simp2d
    #
    wph
    cc0
    cr
    wcel
    #
    @30
    @28
    0re
    wph
    @22
    @23
    @30
    @31
    simp3d
    #
    @27
    @30
    vx
    cc0
    cr
    @24
    cc0
    wceq
    @26
    @29
    vw
    cR
    @24
    cc0
    @25
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    #
    vx
    vw
    cR
    infrecl
    syl3anc
    syl5eqel
    #
    resqcld
    #
    c4
    @3
    remulcl
    sylancr
    #
    wph
    @0
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    cK
    cX
    wcel
    #
    cL
    cX
    wcel
    #
    @0
    cr
    wcel
    wph
    cU
    cnv
    wcel
    #
    @40
    wph
    cU
    ccphlo
    wcel
    #
    @43
    minveco.u
    cU
    phnv
    syl
    #
    cD
    cU
    cX
    minveco.x
    minveco.d
    imsmet
    syl
    #
    wph
    cY
    cX
    cK
    wph
    @43
    cW
    cU
    css
    cfv
    #
    wcel
    #
    cY
    cX
    wss
    @45
    wph
    @47
    ccbn
    cin
    @47
    cW
    @47
    ccbn
    inss1
    minveco.w
    sseldi
    #
    cU
    @47
    cW
    cX
    cY
    minveco.x
    minveco.y
    @47
    eqid
    #
    sspba
    syl2anc
    #
    minvecolem2.3
    sseldd
    #
    wph
    cY
    cX
    cL
    @51
    minvecolem2.4
    sseldd
    #
    cK
    cL
    cD
    cX
    metcl
    syl3anc
    resqcld
    #
    readdcld
    wph
    @17
    @1
    wph
    @19
    @16
    cr
    wcel
    #
    @17
    cr
    wcel
    4re
    wph
    @15
    wph
    @43
    @14
    cX
    wcel
    #
    @15
    cr
    wcel
    #
    @45
    wph
    @43
    cA
    cX
    wcel
    #
    @13
    cX
    wcel
    #
    @56
    @45
    minveco.a
    wph
    cY
    cX
    @13
    @51
    wph
    @9
    @11
    cW
    cns
    cfv
    #
    co
    #
    @13
    cY
    wph
    @43
    @48
    @9
    cc
    wcel
    #
    @11
    cY
    wcel
    #
    @61
    @13
    wceq
    @45
    @49
    c1
    cc
    wcel
    @62
    wph
    ax-1cn
    c1
    halfcl
    mp1i
    #
    wph
    cK
    cL
    cW
    cpv
    cfv
    #
    co
    #
    @11
    cY
    wph
    @43
    @48
    cK
    cY
    wcel
    #
    cL
    cY
    wcel
    #
    @66
    @11
    wceq
    @45
    @49
    minvecolem2.3
    minvecolem2.4
    cK
    cL
    cU
    @65
    @10
    @47
    cW
    cY
    minveco.y
    @10
    eqid
    #
    @65
    eqid
    #
    @50
    sspgval
    syl22anc
    wph
    cW
    cnv
    wcel
    #
    @67
    @68
    @66
    cY
    wcel
    wph
    @43
    @48
    @71
    @45
    @49
    cU
    @47
    cW
    @50
    sspnv
    syl2anc
    #
    minvecolem2.3
    minvecolem2.4
    cK
    cL
    cW
    @65
    cY
    minveco.y
    @70
    nvgcl
    syl3anc
    eqeltrrd
    #
    @9
    @11
    @60
    @12
    cU
    @47
    cW
    cY
    minveco.y
    @12
    eqid
    #
    @60
    eqid
    #
    @50
    sspsval
    syl22anc
    wph
    @71
    @62
    @63
    @61
    cY
    wcel
    @72
    @64
    @73
    @9
    @11
    @60
    cW
    cY
    minveco.y
    @75
    nvscl
    syl3anc
    eqeltrrd
    #
    sseldd
    #
    cA
    @13
    cU
    cM
    cX
    minveco.x
    minveco.m
    nvmcl
    syl3anc
    #
    @14
    cU
    cN
    cX
    minveco.x
    minveco.n
    nvcl
    syl2anc
    #
    resqcld
    #
    c4
    @16
    remulcl
    sylancr
    #
    @54
    readdcld
    wph
    @19
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    4re
    wph
    @3
    cB
    @38
    minvecolem2.1
    readdcld
    #
    c4
    @7
    remulcl
    sylancr
    wph
    @4
    @17
    @1
    @39
    @81
    @54
    wph
    @3
    @16
    cle
    wbr
    #
    @4
    @17
    cle
    wbr
    #
    wph
    cS
    cr
    wcel
    cc0
    cS
    cle
    wbr
    @57
    cS
    @15
    cle
    wbr
    @84
    @37
    wph
    cc0
    @21
    cS
    cle
    wph
    cc0
    @21
    cle
    wbr
    #
    @30
    @35
    wph
    @22
    @23
    @28
    @34
    @86
    @30
    wb
    @32
    @33
    @36
    @34
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
    @79
    wph
    cS
    @21
    @15
    cle
    minveco.s
    wph
    @22
    @28
    @15
    cR
    wcel
    @21
    @15
    cle
    wbr
    @32
    @36
    wph
    @15
    vy
    cY
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
    cmpt
    #
    crn
    #
    cR
    wph
    @15
    @89
    wceq
    #
    vy
    cY
    wrex
    #
    @15
    @91
    wcel
    wph
    @13
    cY
    wcel
    @15
    @15
    wceq
    #
    @93
    @76
    @15
    eqid
    @92
    @94
    vy
    @13
    cY
    @87
    @13
    wceq
    #
    @89
    @15
    @15
    @95
    @88
    @14
    cN
    @87
    @13
    cA
    cM
    oveq2
    fveq2d
    eqeq2d
    rspcev
    sylancl
    vy
    cY
    @89
    @15
    @90
    @90
    eqid
    @88
    cN
    fvex
    elrnmpti
    sylibr
    minveco.r
    syl6eleqr
    vx
    vw
    @15
    cR
    infrelb
    syl3anc
    syl5eqbr
    cS
    @15
    le2sq2
    syl22anc
    wph
    @20
    @55
    @84
    @85
    wb
    #
    @38
    @80
    @20
    @55
    @19
    cc0
    c4
    clt
    wbr
    #
    wa
    @96
    @19
    @97
    4re
    4pos
    pm3.2i
    @3
    @16
    c4
    lemul2
    mp3an3
    syl2anc
    mpbid
    leadd1dd
    wph
    c2
    cA
    cK
    cD
    co
    #
    c2
    cexp
    co
    #
    cA
    cL
    cD
    co
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    c2
    c2
    @7
    cmul
    co
    #
    cmul
    co
    #
    @18
    @8
    cle
    wph
    @102
    @104
    cle
    wbr
    #
    @103
    @105
    cle
    wbr
    #
    wph
    @102
    @7
    @7
    caddc
    co
    @104
    cle
    wph
    @99
    @101
    @7
    @7
    wph
    @98
    wph
    @40
    @58
    @41
    @98
    cr
    wcel
    @46
    minveco.a
    @52
    cA
    cK
    cD
    cX
    metcl
    syl3anc
    resqcld
    #
    wph
    @100
    wph
    @40
    @58
    @42
    @100
    cr
    wcel
    @46
    minveco.a
    @53
    cA
    cL
    cD
    cX
    metcl
    syl3anc
    resqcld
    #
    @83
    @83
    minvecolem2.5
    minvecolem2.6
    le2addd
    wph
    @7
    wph
    @7
    @83
    recnd
    #
    2timesd
    breqtrrd
    wph
    @102
    cr
    wcel
    #
    @104
    cr
    wcel
    #
    @106
    @107
    wb
    #
    wph
    @99
    @101
    @108
    @109
    readdcld
    wph
    c2
    cr
    wcel
    #
    @82
    @112
    2re
    @83
    c2
    @7
    remulcl
    sylancr
    @111
    @112
    @114
    cc0
    c2
    clt
    wbr
    #
    wa
    @113
    @114
    @115
    2re
    2pos
    pm3.2i
    @102
    @104
    c2
    lemul2
    mp3an3
    syl2anc
    mpbid
    wph
    cA
    cK
    cM
    co
    #
    cA
    cL
    cM
    co
    #
    @10
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    @116
    @117
    cM
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @116
    cN
    cfv
    #
    c2
    cexp
    co
    #
    @117
    cN
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @18
    @103
    wph
    @44
    @116
    cX
    wcel
    #
    @117
    cX
    wcel
    #
    @124
    @130
    wceq
    minveco.u
    wph
    @43
    @58
    @41
    @131
    @45
    minveco.a
    @52
    cA
    cK
    cU
    cM
    cX
    minveco.x
    minveco.m
    nvmcl
    syl3anc
    wph
    @43
    @58
    @42
    @132
    @45
    minveco.a
    @53
    cA
    cL
    cU
    cM
    cX
    minveco.x
    minveco.m
    nvmcl
    syl3anc
    @116
    @117
    cU
    @10
    cM
    cN
    cX
    minveco.x
    @69
    minveco.m
    minveco.n
    phpar2
    syl3anc
    wph
    @17
    @120
    @1
    @123
    caddc
    wph
    c2
    @15
    cmul
    co
    #
    c2
    cexp
    co
    #
    @17
    @120
    wph
    @134
    c2
    c2
    cexp
    co
    #
    @16
    cmul
    co
    #
    @17
    wph
    c2
    cc
    wcel
    #
    @15
    cc
    wcel
    @134
    @136
    wceq
    2cn
    wph
    @15
    @79
    recnd
    c2
    @15
    sqmul
    sylancr
    @135
    c4
    @16
    cmul
    sq2
    oveq1i
    syl6eq
    wph
    @133
    @119
    c2
    cexp
    wph
    c2
    @14
    @12
    co
    #
    cN
    cfv
    #
    @133
    @119
    wph
    @139
    c2
    cabs
    cfv
    #
    @15
    cmul
    co
    #
    @133
    wph
    @43
    @137
    @56
    @139
    @141
    wceq
    @45
    @137
    wph
    2cn
    a1i
    #
    @78
    c2
    @14
    @12
    cU
    cN
    cX
    minveco.x
    @74
    minveco.n
    nvs
    syl3anc
    @140
    c2
    @15
    cmul
    @114
    cc0
    c2
    cle
    wbr
    @140
    c2
    wceq
    2re
    0le2
    c2
    absid
    mp2an
    oveq1i
    syl6eq
    wph
    @138
    @118
    cN
    wph
    @138
    c2
    cA
    @12
    co
    #
    c2
    @13
    @12
    co
    #
    cM
    co
    #
    cA
    cA
    @10
    co
    #
    @11
    cM
    co
    #
    @118
    wph
    @43
    @137
    @58
    @59
    @138
    @145
    wceq
    @45
    @142
    minveco.a
    @77
    c2
    cA
    @13
    @12
    cU
    cM
    cX
    minveco.x
    minveco.m
    @74
    nvmdi
    syl13anc
    wph
    @146
    @143
    @11
    @144
    cM
    wph
    @43
    @58
    @146
    @143
    wceq
    @45
    minveco.a
    cA
    @12
    cU
    @10
    cX
    minveco.x
    @69
    @74
    nv2
    syl2anc
    wph
    c2
    @9
    cmul
    co
    #
    @11
    @12
    co
    #
    @11
    @144
    wph
    @149
    c1
    @11
    @12
    co
    #
    @11
    @148
    c1
    @11
    @12
    c2
    2cn
    2ne0
    recidi
    oveq1i
    wph
    @43
    @11
    cX
    wcel
    #
    @150
    @11
    wceq
    @45
    wph
    @43
    @41
    @42
    @151
    @45
    @52
    @53
    cK
    cL
    cU
    @10
    cX
    minveco.x
    @69
    nvgcl
    syl3anc
    #
    @11
    @12
    cU
    cX
    minveco.x
    @74
    nvsid
    syl2anc
    syl5eq
    wph
    @43
    @137
    @62
    @151
    @149
    @144
    wceq
    @45
    @142
    @64
    @152
    c2
    @9
    @11
    @12
    cU
    cX
    minveco.x
    @74
    nvsass
    syl13anc
    eqtr3d
    oveq12d
    wph
    @43
    @58
    @58
    @41
    @42
    @147
    @118
    wceq
    @45
    minveco.a
    minveco.a
    @52
    @53
    cA
    cA
    cK
    cL
    cU
    @10
    cM
    cX
    minveco.x
    @69
    minveco.m
    nvaddsub4
    syl122anc
    3eqtr2d
    fveq2d
    eqtr3d
    oveq1d
    eqtr3d
    wph
    @0
    @122
    c2
    cexp
    wph
    cL
    cK
    cD
    co
    #
    cL
    cK
    cM
    co
    #
    cN
    cfv
    #
    @0
    @122
    wph
    @43
    @42
    @41
    @153
    @155
    wceq
    @45
    @53
    @52
    cL
    cK
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
    wph
    @40
    @41
    @42
    @0
    @153
    wceq
    @46
    @52
    @53
    cK
    cL
    cD
    cX
    metsym
    syl3anc
    wph
    @121
    @154
    cN
    wph
    @43
    @58
    @41
    @42
    @121
    @154
    wceq
    @45
    minveco.a
    @52
    @53
    cA
    cK
    cL
    cU
    cM
    cX
    minveco.x
    minveco.m
    nvnnncan1
    syl13anc
    fveq2d
    3eqtr4d
    oveq1d
    oveq12d
    wph
    @102
    @129
    c2
    cmul
    wph
    @99
    @126
    @101
    @128
    caddc
    wph
    @98
    @125
    c2
    cexp
    wph
    @43
    @58
    @41
    @98
    @125
    wceq
    @45
    minveco.a
    @52
    cA
    cK
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
    oveq1d
    wph
    @100
    @127
    c2
    cexp
    wph
    @43
    @58
    @42
    @100
    @127
    wceq
    @45
    minveco.a
    @53
    cA
    cL
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
    oveq1d
    oveq12d
    oveq2d
    3eqtr4d
    wph
    @8
    c2
    c2
    cmul
    co
    #
    @7
    cmul
    co
    @105
    @156
    c4
    @7
    cmul
    2t2e4
    oveq1i
    wph
    c2
    c2
    @7
    @142
    @142
    @110
    mulassd
    syl5eqr
    3brtr4d
    letrd
    wph
    c4
    @3
    cB
    c4
    cc
    wcel
    wph
    4cn
    a1i
    wph
    @3
    @38
    recnd
    wph
    cB
    minvecolem2.1
    recnd
    adddid
    breqtrd
    wph
    @1
    @2
    @4
    @54
    wph
    @19
    cB
    cr
    wcel
    @2
    cr
    wcel
    4re
    minvecolem2.1
    c4
    cB
    remulcl
    sylancr
    @39
    leadd2d
    mpbird
end
