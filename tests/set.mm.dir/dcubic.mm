include "c3.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "cdiv.mm"
include "cmin.mm"
include "wa.mm"
include "cc.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "c2.mm"
include "c4.mm"
include "csqrt.mm"
include "cfv.mm"
include "wn.mm"
include "wne.mm"
include "adantr.mm"
include "wcel.mm"
include "wi.mm"
include "cz.mm"
include "3z.mm"
include "expne0i.mm"
include "mp3an3.mm"
include "ex.mm"
include "syl.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "oveq2d.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cn.mm"
include "3nn.mm"
include "0exp.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "simplr.mm"
include "0cnd.mm"
include "eqeltrd.mm"
include "addcld.mm"
include "addid2d.mm"
include "3eqtr3rd.mm"
include "2cn.mm"
include "2ne0.mm"
include "div0i.mm"
include "sq0id.mm"
include "3cn.mm"
include "a1i.mm"
include "3ne0.mm"
include "divcld.mm"
include "4cn.mm"
include "4ne0.mm"
include "sqcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "simprr.mm"
include "sqr00d.mm"
include "mul01i.mm"
include "syl6eqr.mm"
include "mulcanad.mm"
include "oveq12d.mm"
include "00id.mm"
include "sqeq0d.mm"
include "0m0e0.mm"
include "necon3ad.mm"
include "syld.mm"
include "mpd.mm"
include "oveq12.mm"
include "jca.mm"
include "sqrtcld.mm"
include "halfaddsub.mm"
include "syl2anc.mm"
include "simpld.mm"
include "eqeq1d.mm"
include "simprd.mm"
include "anbi12d.mm"
include "syl5ib.mm"
include "con3d.mm"
include "wo.mm"
include "eldifi.mm"
include "adantl.mm"
include "eldifsni.mm"
include "subaddd.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "mulcld.mm"
include "subeq0ad.mm"
include "sqvald.mm"
include "adddird.mm"
include "divcan1d.mm"
include "addcomd.mm"
include "3eqtrrd.mm"
include "eqeq12d.mm"
include "mulcan2d.mm"
include "3bitrd.mm"
include "cneg.mm"
include "1cnd.mm"
include "ax-1ne0.mm"
include "negcld.mm"
include "sqneg.mm"
include "mulid2d.mm"
include "mulneg2.mm"
include "subnegd.mm"
include "eqtr2d.mm"
include "quad.mm"
include "mulneg1d.mm"
include "negdid.mm"
include "eqtr4d.mm"
include "negsubd.mm"
include "negnegd.mm"
include "2t1e2.mm"
include "eqeq2d.mm"
include "orbi12d.mm"
include "3bitr3d.mm"
include "3bitr2d.mm"
include "rexbidva.mm"
include "r19.43.mm"
include "syl6bb.mm"
include "risset.mm"
include "wb.mm"
include "halfcld.mm"
include "eldifsn.mm"
include "baib.mm"
include "syl5bbr.mm"
include "subcld.mm"
include "neorian.mm"
include "bitrd.mm"
include "sylibrd.mm"
include "imp.mm"
include "syldan.mm"
include "ad2antrl.mm"
include "dcubic2.mm"
include "rexlimddv.mm"
include "cn0.mm"
include "3nn0.mm"
include "mulexpd.mm"
include "expcl.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "eqnetrd.mm"
include "oveq1.mm"
include "necon3i.mm"
include "mulne0d.mm"
include "dcubic1.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem dcubic
  let wph: wff ph
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vu: setvar u
  let cU: class U
  assume dcubic.c: |- ( ph -> P e. CC )
  assume dcubic.d: |- ( ph -> Q e. CC )
  assume dcubic.x: |- ( ph -> X e. CC )
  assume dcubic.t: |- ( ph -> T e. CC )
  assume dcubic.3: |- ( ph -> ( T ^ 3 ) = ( G - N ) )
  assume dcubic.g: |- ( ph -> G e. CC )
  assume dcubic.2: |- ( ph -> ( G ^ 2 ) = ( ( N ^ 2 ) + ( M ^ 3 ) ) )
  assume dcubic.m: |- ( ph -> M = ( P / 3 ) )
  assume dcubic.n: |- ( ph -> N = ( Q / 2 ) )
  assume dcubic.0: |- ( ph -> T =/= 0 )

  disjoint M r
  disjoint P r
  disjoint ph r
  disjoint Q r
  disjoint T r
  disjoint X r
  disjoint r u
  disjoint M u
  disjoint P u
  disjoint ph u
  disjoint Q u
  disjoint T u
  disjoint U r
  disjoint X u
  assert |- ( ph -> ( ( ( X ^ 3 ) + ( ( P x. X ) + Q ) ) = 0 <-> E. r e. CC ( ( r ^ 3 ) = 1 /\ X = ( ( r x. T ) - ( M / ( r x. T ) ) ) ) ) )

  proof
    wph
    cX
    c3
    cexp
    co
    #
    cP
    cX
    cmul
    co
    #
    cQ
    caddc
    co
    #
    caddc
    co
    #
    cc0
    wceq
    #
    vr
    cv
    #
    c3
    cexp
    co
    #
    c1
    wceq
    #
    cX
    @5
    cT
    cmul
    co
    #
    cM
    @8
    cdiv
    co
    cmin
    co
    wceq
    #
    wa
    #
    vr
    cc
    wrex
    #
    wph
    @4
    @11
    wph
    @4
    wa
    #
    cX
    vu
    cv
    #
    cM
    @13
    cdiv
    co
    #
    cmin
    co
    #
    wceq
    #
    @11
    vu
    cc
    cc0
    csn
    #
    cdif
    #
    wph
    @4
    cX
    cc0
    wceq
    #
    cX
    c2
    cexp
    co
    #
    c4
    cM
    cmul
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @16
    vu
    @18
    wrex
    #
    @12
    cT
    cc0
    wne
    #
    @26
    wph
    @28
    @4
    dcubic.0
    adantr
    @12
    @28
    cT
    c3
    cexp
    co
    #
    cc0
    wne
    #
    @26
    @12
    cT
    cc
    wcel
    #
    @28
    @30
    wi
    wph
    @31
    @4
    dcubic.t
    adantr
    @31
    @28
    @30
    @31
    @28
    c3
    cz
    wcel
    @30
    3z
    cT
    c3
    expne0i
    mp3an3
    ex
    syl
    @12
    @25
    @29
    cc0
    @12
    @25
    @29
    cc0
    wceq
    @12
    @25
    wa
    #
    @29
    cG
    cN
    cmin
    co
    #
    cc0
    wph
    @29
    @33
    wceq
    #
    @4
    @25
    dcubic.3
    ad2antrr
    @32
    @33
    cc0
    cc0
    cmin
    co
    #
    cc0
    @32
    cG
    cc0
    cN
    cc0
    cmin
    @32
    cG
    wph
    cG
    cc
    wcel
    #
    @4
    @25
    dcubic.g
    ad2antrr
    @32
    cG
    c2
    cexp
    co
    #
    cN
    c2
    cexp
    co
    #
    cM
    c3
    cexp
    co
    #
    caddc
    co
    #
    cc0
    wph
    @37
    @40
    wceq
    #
    @4
    @25
    dcubic.2
    ad2antrr
    @32
    @40
    cc0
    cc0
    caddc
    co
    #
    cc0
    @32
    @38
    cc0
    @39
    cc0
    caddc
    @32
    cN
    @32
    cN
    cQ
    c2
    cdiv
    co
    #
    cc0
    wph
    cN
    @43
    wceq
    #
    @4
    @25
    dcubic.n
    ad2antrr
    @32
    @43
    cc0
    c2
    cdiv
    co
    cc0
    @32
    cQ
    cc0
    c2
    cdiv
    @32
    @2
    cc0
    cQ
    caddc
    co
    cc0
    cQ
    @32
    @1
    cc0
    cQ
    caddc
    @32
    @1
    cP
    cc0
    cmul
    co
    cc0
    @32
    cX
    cc0
    cP
    cmul
    @12
    @19
    @24
    simprl
    #
    oveq2d
    @32
    cP
    wph
    cP
    cc
    wcel
    #
    @4
    @25
    dcubic.c
    ad2antrr
    mul01d
    eqtrd
    #
    oveq1d
    @32
    @3
    cc0
    @2
    caddc
    co
    cc0
    @2
    @32
    @0
    cc0
    @2
    caddc
    @32
    @0
    cc0
    c3
    cexp
    co
    #
    cc0
    @32
    cX
    cc0
    c3
    cexp
    @45
    oveq1d
    c3
    cn
    wcel
    @48
    cc0
    wceq
    3nn
    c3
    0exp
    ax-mp
    #
    syl6eq
    oveq1d
    wph
    @4
    @25
    simplr
    @32
    @2
    @32
    @1
    cQ
    @32
    @1
    cc0
    cc
    @47
    @32
    0cnd
    #
    eqeltrd
    wph
    cQ
    cc
    wcel
    #
    @4
    @25
    dcubic.d
    ad2antrr
    #
    addcld
    addid2d
    3eqtr3rd
    @32
    cQ
    @52
    addid2d
    3eqtr3rd
    oveq1d
    c2
    2cn
    2ne0
    div0i
    syl6eq
    eqtrd
    #
    sq0id
    @32
    @39
    @48
    cc0
    @32
    cM
    cc0
    c3
    cexp
    @32
    cM
    cc0
    c4
    wph
    cM
    cc
    wcel
    #
    @4
    @25
    wph
    cM
    cP
    c3
    cdiv
    co
    #
    cc
    dcubic.m
    wph
    cP
    c3
    dcubic.c
    c3
    cc
    wcel
    wph
    3cn
    a1i
    c3
    cc0
    wne
    wph
    3ne0
    a1i
    divcld
    eqeltrd
    #
    ad2antrr
    @50
    c4
    cc
    wcel
    #
    @32
    4cn
    a1i
    c4
    cc0
    wne
    @32
    4ne0
    a1i
    @32
    @21
    cc0
    c4
    cc0
    cmul
    co
    @32
    @22
    cc0
    @21
    caddc
    co
    cc0
    @21
    @32
    @20
    cc0
    @21
    caddc
    @32
    cX
    @45
    sq0id
    oveq1d
    @32
    @22
    wph
    @22
    cc
    wcel
    @4
    @25
    wph
    @20
    @21
    wph
    cX
    dcubic.x
    sqcld
    #
    wph
    @57
    @54
    @21
    cc
    wcel
    #
    4cn
    @56
    c4
    cM
    mulcl
    sylancr
    #
    addcld
    #
    ad2antrr
    @12
    @19
    @24
    simprr
    sqr00d
    @32
    @21
    wph
    @59
    @4
    @25
    @60
    ad2antrr
    addid2d
    3eqtr3rd
    c4
    4cn
    mul01i
    syl6eqr
    mulcanad
    oveq1d
    @49
    syl6eq
    oveq12d
    00id
    syl6eq
    eqtrd
    sqeq0d
    @53
    oveq12d
    0m0e0
    syl6eq
    eqtrd
    ex
    necon3ad
    syld
    mpd
    wph
    @26
    @27
    wph
    @26
    cX
    @23
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cc0
    wceq
    cX
    @23
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cc0
    wceq
    wa
    #
    wn
    #
    @27
    wph
    @66
    @25
    @66
    @63
    @65
    caddc
    co
    #
    cc0
    wceq
    #
    @63
    @65
    cmin
    co
    #
    cc0
    wceq
    #
    wa
    wph
    @25
    @66
    @69
    @71
    @66
    @68
    @42
    cc0
    @63
    cc0
    @65
    cc0
    caddc
    oveq12
    00id
    syl6eq
    @66
    @70
    @35
    cc0
    @63
    cc0
    @65
    cc0
    cmin
    oveq12
    0m0e0
    syl6eq
    jca
    wph
    @69
    @19
    @71
    @24
    wph
    @68
    cX
    cc0
    wph
    @68
    cX
    wceq
    #
    @70
    @23
    wceq
    #
    wph
    cX
    cc
    wcel
    #
    @23
    cc
    wcel
    @72
    @73
    wa
    dcubic.x
    wph
    @22
    @61
    sqrtcld
    #
    cX
    @23
    halfaddsub
    syl2anc
    #
    simpld
    eqeq1d
    wph
    @70
    @23
    cc0
    wph
    @72
    @73
    @76
    simprd
    eqeq1d
    anbi12d
    syl5ib
    con3d
    wph
    @27
    @13
    @63
    wceq
    #
    vu
    @18
    wrex
    #
    @13
    @65
    wceq
    #
    vu
    @18
    wrex
    #
    wo
    #
    @67
    wph
    @27
    @77
    @79
    wo
    #
    vu
    @18
    wrex
    @81
    wph
    @16
    @82
    vu
    @18
    wph
    @13
    @18
    wcel
    #
    wa
    #
    @16
    @13
    @14
    cX
    caddc
    co
    #
    wceq
    #
    @13
    c2
    cexp
    co
    #
    cX
    @13
    cmul
    co
    #
    cM
    caddc
    co
    #
    cmin
    co
    #
    cc0
    wceq
    #
    @82
    @84
    @15
    cX
    wceq
    @85
    @13
    wceq
    @16
    @86
    @84
    @13
    @14
    cX
    @83
    @13
    cc
    wcel
    #
    wph
    @13
    cc
    @17
    eldifi
    #
    adantl
    #
    @84
    cM
    @13
    wph
    @54
    @83
    @56
    adantr
    #
    @94
    @83
    @13
    cc0
    wne
    #
    wph
    @13
    cc
    cc0
    eldifsni
    #
    adantl
    #
    divcld
    #
    wph
    @74
    @83
    dcubic.x
    adantr
    #
    subaddd
    cX
    @15
    eqcom
    @13
    @85
    eqcom
    3bitr4g
    @84
    @91
    @87
    @89
    wceq
    @13
    @13
    cmul
    co
    #
    @85
    @13
    cmul
    co
    #
    wceq
    @86
    @84
    @87
    @89
    @84
    @13
    @94
    sqcld
    #
    @84
    @88
    cM
    @84
    cX
    @13
    @100
    @94
    mulcld
    #
    @95
    addcld
    #
    subeq0ad
    @84
    @87
    @101
    @89
    @102
    @84
    @13
    @94
    sqvald
    @84
    @102
    @14
    @13
    cmul
    co
    #
    @88
    caddc
    co
    cM
    @88
    caddc
    co
    @89
    @84
    @14
    cX
    @13
    @99
    @100
    @94
    adddird
    @84
    @106
    cM
    @88
    caddc
    @84
    cM
    @13
    @95
    @94
    @98
    divcan1d
    oveq1d
    @84
    cM
    @88
    @95
    @104
    addcomd
    3eqtrrd
    eqeq12d
    @84
    @13
    @85
    @13
    @94
    @84
    @14
    cX
    @99
    @100
    addcld
    @94
    @98
    mulcan2d
    3bitrd
    @84
    c1
    @87
    cmul
    co
    #
    cX
    cneg
    #
    @13
    cmul
    co
    #
    cM
    cneg
    #
    caddc
    co
    #
    caddc
    co
    #
    cc0
    wceq
    @13
    @108
    cneg
    #
    @23
    caddc
    co
    #
    c2
    c1
    cmul
    co
    #
    cdiv
    co
    #
    wceq
    #
    @13
    @113
    @23
    cmin
    co
    #
    @115
    cdiv
    co
    #
    wceq
    #
    wo
    @91
    @82
    @84
    c1
    @108
    @110
    @22
    @13
    @84
    1cnd
    c1
    cc0
    wne
    #
    @84
    ax-1ne0
    a1i
    wph
    @108
    cc
    wcel
    @83
    wph
    cX
    dcubic.x
    negcld
    adantr
    wph
    @110
    cc
    wcel
    @83
    wph
    cM
    @56
    negcld
    adantr
    #
    @94
    @84
    @108
    c2
    cexp
    co
    #
    c4
    c1
    @110
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    @20
    @21
    cneg
    #
    cmin
    co
    @22
    @84
    @123
    @20
    @125
    @126
    cmin
    @84
    @74
    @123
    @20
    wceq
    @100
    cX
    sqneg
    syl
    @84
    @125
    c4
    @110
    cmul
    co
    #
    @126
    @84
    @124
    @110
    c4
    cmul
    @84
    @110
    @122
    mulid2d
    oveq2d
    @84
    @57
    @54
    @127
    @126
    wceq
    4cn
    @95
    c4
    cM
    mulneg2
    sylancr
    eqtrd
    oveq12d
    @84
    @20
    @21
    wph
    @20
    cc
    wcel
    @83
    @58
    adantr
    wph
    @59
    @83
    @60
    adantr
    subnegd
    eqtr2d
    quad
    @84
    @112
    @90
    cc0
    @84
    @112
    @87
    @89
    cneg
    #
    caddc
    co
    @90
    @84
    @107
    @87
    @111
    @128
    caddc
    @84
    @87
    @103
    mulid2d
    @84
    @111
    @88
    cneg
    #
    @110
    caddc
    co
    @128
    @84
    @109
    @129
    @110
    caddc
    @84
    cX
    @13
    @100
    @94
    mulneg1d
    oveq1d
    @84
    @88
    cM
    @104
    @95
    negdid
    eqtr4d
    oveq12d
    @84
    @87
    @89
    @103
    @105
    negsubd
    eqtrd
    eqeq1d
    @84
    @117
    @77
    @120
    @79
    @84
    @116
    @63
    @13
    @84
    @114
    @62
    @115
    c2
    cdiv
    @84
    @113
    cX
    @23
    caddc
    @84
    cX
    @100
    negnegd
    #
    oveq1d
    @115
    c2
    wceq
    @84
    2t1e2
    a1i
    #
    oveq12d
    eqeq2d
    @84
    @119
    @65
    @13
    @84
    @118
    @64
    @115
    c2
    cdiv
    @84
    @113
    cX
    @23
    cmin
    @130
    oveq1d
    @131
    oveq12d
    eqeq2d
    orbi12d
    3bitr3d
    3bitr2d
    rexbidva
    @77
    @79
    vu
    @18
    r19.43
    syl6bb
    wph
    @81
    @63
    cc0
    wne
    #
    @65
    cc0
    wne
    #
    wo
    @67
    wph
    @78
    @132
    @80
    @133
    @78
    @63
    @18
    wcel
    #
    wph
    @132
    vu
    @63
    @18
    risset
    wph
    @63
    cc
    wcel
    #
    @134
    @132
    wb
    wph
    @62
    wph
    cX
    @23
    dcubic.x
    @75
    addcld
    halfcld
    @134
    @135
    @132
    @63
    cc
    cc0
    eldifsn
    baib
    syl
    syl5bbr
    @80
    @65
    @18
    wcel
    #
    wph
    @133
    vu
    @65
    @18
    risset
    wph
    @65
    cc
    wcel
    #
    @136
    @133
    wb
    wph
    @64
    wph
    cX
    @23
    dcubic.x
    @75
    subcld
    halfcld
    @136
    @137
    @133
    @65
    cc
    cc0
    eldifsn
    baib
    syl
    syl5bbr
    orbi12d
    @63
    cc0
    @65
    cc0
    neorian
    syl6bb
    bitrd
    sylibrd
    imp
    syldan
    @12
    @83
    @16
    wa
    #
    wa
    cP
    cQ
    cT
    @13
    cG
    cM
    cN
    cX
    vr
    wph
    @46
    @4
    @138
    dcubic.c
    ad2antrr
    wph
    @51
    @4
    @138
    dcubic.d
    ad2antrr
    wph
    @74
    @4
    @138
    dcubic.x
    ad2antrr
    wph
    @31
    @4
    @138
    dcubic.t
    ad2antrr
    wph
    @34
    @4
    @138
    dcubic.3
    ad2antrr
    wph
    @36
    @4
    @138
    dcubic.g
    ad2antrr
    wph
    @41
    @4
    @138
    dcubic.2
    ad2antrr
    wph
    cM
    @55
    wceq
    #
    @4
    @138
    dcubic.m
    ad2antrr
    wph
    @44
    @4
    @138
    dcubic.n
    ad2antrr
    wph
    @28
    @4
    @138
    dcubic.0
    ad2antrr
    @83
    @92
    @12
    @16
    @93
    ad2antrl
    @83
    @96
    @12
    @16
    @97
    ad2antrl
    @12
    @83
    @16
    simprr
    wph
    @4
    @138
    simplr
    dcubic2
    rexlimddv
    ex
    wph
    @10
    @4
    vr
    cc
    wph
    @5
    cc
    wcel
    #
    wa
    #
    @10
    @4
    @141
    @10
    wa
    #
    cP
    cQ
    @8
    cG
    cM
    cN
    cX
    wph
    @46
    @140
    @10
    dcubic.c
    ad2antrr
    wph
    @51
    @140
    @10
    dcubic.d
    ad2antrr
    wph
    @74
    @140
    @10
    dcubic.x
    ad2antrr
    @142
    @5
    cT
    wph
    @140
    @10
    simplr
    #
    wph
    @31
    @140
    @10
    dcubic.t
    ad2antrr
    #
    mulcld
    @142
    @8
    c3
    cexp
    co
    @6
    @29
    cmul
    co
    c1
    @29
    cmul
    co
    #
    @33
    @142
    @5
    cT
    c3
    @143
    @144
    c3
    cn0
    wcel
    #
    @142
    3nn0
    a1i
    mulexpd
    @142
    @6
    c1
    @29
    cmul
    @141
    @7
    @9
    simprl
    #
    oveq1d
    wph
    @145
    @33
    wceq
    @140
    @10
    wph
    @145
    @29
    @33
    wph
    @29
    wph
    @31
    @146
    @29
    cc
    wcel
    dcubic.t
    3nn0
    cT
    c3
    expcl
    sylancl
    mulid2d
    dcubic.3
    eqtrd
    ad2antrr
    3eqtrd
    wph
    @36
    @140
    @10
    dcubic.g
    ad2antrr
    wph
    @41
    @140
    @10
    dcubic.2
    ad2antrr
    wph
    @139
    @140
    @10
    dcubic.m
    ad2antrr
    wph
    @44
    @140
    @10
    dcubic.n
    ad2antrr
    @142
    @5
    cT
    @143
    @144
    @142
    @6
    cc0
    wne
    @5
    cc0
    wne
    @142
    @6
    c1
    cc0
    @147
    @121
    @142
    ax-1ne0
    a1i
    eqnetrd
    @5
    cc0
    @6
    cc0
    @5
    cc0
    wceq
    @6
    @48
    cc0
    @5
    cc0
    c3
    cexp
    oveq1
    @49
    syl6eq
    necon3i
    syl
    wph
    @28
    @140
    @10
    dcubic.0
    ad2antrr
    mulne0d
    @141
    @7
    @9
    simprr
    dcubic1
    ex
    rexlimdva
    impbid
end
