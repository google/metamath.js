include "cn0.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "eqeltrrd.mm"
include "nnnn0d.mm"
include "cv.mm"
include "cc0.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "wn.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "cfzo.mm"
include "co.mm"
include "cword.mm"
include "wf.mm"
include "wrdf.mm"
include "syl.mm"
include "clt.mm"
include "wbr.mm"
include "0nn0.mm"
include "a1i.mm"
include "nngt0d.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "cpmtr.mm"
include "eqid.mm"
include "pmtrfmvdn0.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "cgsu.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wrex.mm"
include "fzonel.mm"
include "simpr1.mm"
include "mto.mm"
include "nrex.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "eleq1.mm"
include "fveq2.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "3anbi123d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi2d.mm"
include "weq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "notbid.mm"
include "ralbidv.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "3anbi23d.mm"
include "cbvrexv.mm"
include "adantr.mm"
include "jca.mm"
include "simpr.mm"
include "ral0.mm"
include "fzo0.mm"
include "raleqi.mm"
include "mpbir.mm"
include "3jca.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simpll.mm"
include "ad2antll.mm"
include "simplr.mm"
include "simpr2.mm"
include "simpr3.mm"
include "c2.mm"
include "cmin.mm"
include "sylnib.mm"
include "psgnunilem2.mm"
include "rexlimdvaa.mm"
include "a2i.mm"
include "nn0ind.mm"
include "mtoi.mm"
include "con2i.mm"
include "exlimddv.mm"
include "pm2.65i.mm"

theorem psgnunilem3
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cT: class T
  let cG: class G
  let cL: class L
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vw: setvar w
  let vy: setvar y
  assume psgnunilem3.g: |- G = ( SymGrp ` D )
  assume psgnunilem3.t: |- T = ran ( pmTrsp ` D )
  assume psgnunilem3.d: |- ( ph -> D e. V )
  assume psgnunilem3.w1: |- ( ph -> W e. Word T )
  assume psgnunilem3.l: |- ( ph -> ( # ` W ) = L )
  assume psgnunilem3.w2: |- ( ph -> ( # ` W ) e. NN )
  assume psgnunilem3.w3: |- ( ph -> ( G gsum W ) = ( _I |` D ) )
  assume psgnunilem3.in: |- ( ph -> -. E. x e. Word T ( ( # ` x ) = ( L - 2 ) /\ ( G gsum x ) = ( _I |` D ) ) )

  disjoint D x
  disjoint G x
  disjoint L x
  disjoint T x
  disjoint W x
  disjoint ph x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint D a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint D b
  disjoint c d
  disjoint c e
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint D c
  disjoint d e
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint D d
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint D e
  disjoint w x
  disjoint w y
  disjoint D w
  disjoint x y
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G d
  disjoint G w
  disjoint L a
  disjoint L b
  disjoint L c
  disjoint L e
  disjoint L w
  disjoint L y
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T w
  disjoint T y
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W e
  disjoint W w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint e ph
  disjoint G y
  assert |- -. ph

  proof
    wph
    cL
    cn0
    wcel
    #
    wph
    cL
    wph
    cW
    chash
    cfv
    #
    cL
    cn
    psgnunilem3.l
    psgnunilem3.w2
    eqeltrrd
    #
    nnnn0d
    wph
    ve
    cv
    #
    cc0
    cW
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    @0
    wn
    ve
    wph
    @6
    c0
    wne
    #
    @7
    ve
    wex
    wph
    @4
    cT
    wcel
    @8
    wph
    cc0
    @1
    cfzo
    co
    #
    cT
    cc0
    cW
    wph
    cW
    cT
    cword
    #
    wcel
    #
    @9
    cT
    cW
    wf
    psgnunilem3.w1
    cT
    cW
    wrdf
    syl
    wph
    cc0
    cc0
    cL
    cfzo
    co
    #
    @9
    wph
    cc0
    cn0
    wcel
    #
    cL
    cn
    wcel
    cc0
    cL
    clt
    wbr
    cc0
    @12
    wcel
    #
    @13
    wph
    0nn0
    a1i
    @2
    wph
    cL
    @2
    nngt0d
    cc0
    cL
    elfzo0
    syl3anbrc
    #
    wph
    @1
    cL
    cc0
    cfzo
    psgnunilem3.l
    oveq2d
    eleqtrrd
    ffvelrnd
    cD
    cT
    cD
    cpmtr
    cfv
    #
    @4
    @16
    eqid
    psgnunilem3.t
    pmtrfmvdn0
    syl
    ve
    @6
    n0
    sylib
    @0
    wph
    @7
    wa
    #
    @0
    @17
    cG
    vw
    cv
    #
    cgsu
    co
    #
    cid
    cD
    cres
    #
    wceq
    #
    @18
    chash
    cfv
    #
    cL
    wceq
    #
    wa
    #
    cL
    @12
    wcel
    #
    @3
    cL
    @18
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    @3
    vc
    cv
    #
    @18
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    vc
    @12
    wral
    #
    w3a
    #
    wa
    #
    vw
    @10
    wrex
    #
    @38
    vw
    @10
    @38
    wn
    @18
    @10
    wcel
    @38
    @25
    cc0
    cL
    fzonel
    @24
    @25
    @29
    @36
    simpr1
    mto
    a1i
    nrex
    @17
    @24
    va
    cv
    #
    @12
    wcel
    #
    @3
    @40
    @18
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    @35
    vc
    cc0
    @40
    cfzo
    co
    #
    wral
    #
    w3a
    #
    wa
    #
    vw
    @10
    wrex
    #
    wi
    @17
    @24
    @14
    @3
    cc0
    @18
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    @35
    vc
    cc0
    cc0
    cfzo
    co
    #
    wral
    #
    w3a
    #
    wa
    #
    vw
    @10
    wrex
    #
    wi
    @17
    cG
    vx
    cv
    #
    cgsu
    co
    #
    @20
    wceq
    #
    @60
    chash
    cfv
    #
    cL
    wceq
    #
    wa
    #
    vb
    cv
    #
    @12
    wcel
    #
    @3
    @66
    @60
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    @3
    vd
    cv
    #
    @60
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    vd
    cc0
    @66
    cfzo
    co
    #
    wral
    #
    w3a
    #
    wa
    #
    vx
    @10
    wrex
    #
    wi
    #
    @17
    @24
    @66
    c1
    caddc
    co
    #
    @12
    wcel
    #
    @3
    @84
    @18
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    @35
    vc
    cc0
    @84
    cfzo
    co
    #
    wral
    #
    w3a
    #
    wa
    #
    vw
    @10
    wrex
    #
    wi
    #
    @17
    @39
    wi
    va
    vb
    cL
    @40
    cc0
    wceq
    #
    @50
    @59
    @17
    @96
    @49
    @58
    vw
    @10
    @96
    @48
    @57
    @24
    @96
    @41
    @14
    @45
    @54
    @47
    @56
    @40
    cc0
    @12
    eleq1
    @96
    @44
    @53
    @3
    @96
    @43
    @52
    @96
    @42
    @51
    cid
    @40
    cc0
    @18
    fveq2
    difeq1d
    dmeqd
    eleq2d
    @96
    @35
    vc
    @46
    @55
    @40
    cc0
    cc0
    cfzo
    oveq2
    raleqdv
    3anbi123d
    anbi2d
    rexbidv
    imbi2d
    va
    vb
    weq
    #
    @50
    @82
    @17
    @97
    @50
    @24
    @67
    @3
    @66
    @18
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    @35
    vc
    @78
    wral
    #
    w3a
    #
    wa
    #
    vw
    @10
    wrex
    @82
    @97
    @49
    @104
    vw
    @10
    @97
    @48
    @103
    @24
    @97
    @41
    @67
    @45
    @101
    @47
    @102
    @40
    @66
    @12
    eleq1
    @97
    @44
    @100
    @3
    @97
    @43
    @99
    @97
    @42
    @98
    cid
    @40
    @66
    @18
    fveq2
    difeq1d
    dmeqd
    eleq2d
    @97
    @35
    vc
    @46
    @78
    @40
    @66
    cc0
    cfzo
    oveq2
    raleqdv
    3anbi123d
    anbi2d
    rexbidv
    @104
    @81
    vw
    vx
    @10
    vw
    vx
    weq
    #
    @24
    @65
    @103
    @80
    @105
    @21
    @62
    @23
    @64
    @105
    @19
    @61
    @20
    @18
    @60
    cG
    cgsu
    oveq2
    eqeq1d
    @105
    @22
    @63
    cL
    @18
    @60
    chash
    fveq2
    eqeq1d
    anbi12d
    @105
    @101
    @71
    @102
    @79
    @67
    @105
    @100
    @70
    @3
    @105
    @99
    @69
    @105
    @98
    @68
    cid
    @66
    @18
    @60
    fveq1
    difeq1d
    dmeqd
    eleq2d
    @105
    @102
    @3
    @30
    @60
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    vc
    @78
    wral
    @79
    @105
    @35
    @110
    vc
    @78
    @105
    @34
    @109
    @105
    @33
    @108
    @3
    @105
    @32
    @107
    @105
    @31
    @106
    cid
    @30
    @18
    @60
    fveq1
    difeq1d
    dmeqd
    eleq2d
    notbid
    ralbidv
    @110
    @77
    vc
    vd
    @78
    vc
    vd
    weq
    #
    @109
    @76
    @111
    @108
    @75
    @3
    @111
    @107
    @74
    @111
    @106
    @73
    cid
    @30
    @72
    @60
    fveq2
    difeq1d
    dmeqd
    eleq2d
    notbid
    cbvralv
    syl6bb
    3anbi23d
    anbi12d
    cbvrexv
    syl6bb
    imbi2d
    @40
    @84
    wceq
    #
    @50
    @94
    @17
    @112
    @49
    @93
    vw
    @10
    @112
    @48
    @92
    @24
    @112
    @41
    @85
    @45
    @89
    @47
    @91
    @40
    @84
    @12
    eleq1
    @112
    @44
    @88
    @3
    @112
    @43
    @87
    @112
    @42
    @86
    cid
    @40
    @84
    @18
    fveq2
    difeq1d
    dmeqd
    eleq2d
    @112
    @35
    vc
    @46
    @90
    @40
    @84
    cc0
    cfzo
    oveq2
    raleqdv
    3anbi123d
    anbi2d
    rexbidv
    imbi2d
    @40
    cL
    wceq
    #
    @50
    @39
    @17
    @113
    @49
    @38
    vw
    @10
    @113
    @48
    @37
    @24
    @113
    @41
    @25
    @45
    @29
    @47
    @36
    @40
    cL
    @12
    eleq1
    @113
    @44
    @28
    @3
    @113
    @43
    @27
    @113
    @42
    @26
    cid
    @40
    cL
    @18
    fveq2
    difeq1d
    dmeqd
    eleq2d
    @113
    @35
    vc
    @46
    @12
    @40
    cL
    cc0
    cfzo
    oveq2
    raleqdv
    3anbi123d
    anbi2d
    rexbidv
    imbi2d
    @17
    @11
    cG
    cW
    cgsu
    co
    #
    @20
    wceq
    #
    @1
    cL
    wceq
    #
    wa
    #
    @14
    @7
    @3
    @30
    cW
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    wcel
    #
    wn
    #
    vc
    @55
    wral
    #
    w3a
    #
    @59
    wph
    @11
    @7
    psgnunilem3.w1
    adantr
    wph
    @117
    @7
    wph
    @115
    @116
    psgnunilem3.w3
    psgnunilem3.l
    jca
    adantr
    @17
    @14
    @7
    @123
    wph
    @14
    @7
    @15
    adantr
    wph
    @7
    simpr
    @123
    @17
    @123
    @122
    vc
    c0
    wral
    @122
    vc
    ral0
    @122
    vc
    @55
    c0
    cc0
    fzo0
    raleqi
    mpbir
    a1i
    3jca
    @58
    @117
    @124
    wa
    vw
    cW
    @10
    @18
    cW
    wceq
    #
    @24
    @117
    @57
    @124
    @125
    @21
    @115
    @23
    @116
    @125
    @19
    @114
    @20
    @18
    cW
    cG
    cgsu
    oveq2
    eqeq1d
    @125
    @22
    @1
    cL
    @18
    cW
    chash
    fveq2
    eqeq1d
    anbi12d
    @125
    @54
    @7
    @56
    @123
    @14
    @125
    @53
    @6
    @3
    @125
    @52
    @5
    @125
    @51
    @4
    cid
    cc0
    @18
    cW
    fveq1
    difeq1d
    dmeqd
    eleq2d
    @125
    @35
    @122
    vc
    @55
    @125
    @34
    @121
    @125
    @33
    @120
    @3
    @125
    @32
    @119
    @125
    @31
    @118
    cid
    @30
    @18
    cW
    fveq1
    difeq1d
    dmeqd
    eleq2d
    notbid
    ralbidv
    3anbi23d
    anbi12d
    rspcev
    syl12anc
    @83
    @95
    wi
    @66
    cn0
    wcel
    @17
    @82
    @94
    @17
    @81
    @94
    vx
    @10
    @17
    @60
    @10
    wcel
    #
    @81
    wa
    #
    wa
    vy
    vw
    @3
    cD
    cT
    vc
    vd
    cG
    @66
    cL
    cV
    @60
    psgnunilem3.g
    psgnunilem3.t
    wph
    cD
    cV
    wcel
    @7
    @127
    psgnunilem3.d
    ad2antrr
    @17
    @126
    @81
    simprl
    @81
    @62
    @17
    @126
    @62
    @64
    @80
    simpll
    ad2antll
    @81
    @64
    @17
    @126
    @62
    @64
    @80
    simplr
    ad2antll
    @81
    @67
    @17
    @126
    @65
    @67
    @71
    @79
    simpr1
    ad2antll
    @81
    @71
    @17
    @126
    @65
    @67
    @71
    @79
    simpr2
    ad2antll
    @81
    @79
    @17
    @126
    @65
    @67
    @71
    @79
    simpr3
    ad2antll
    wph
    vy
    cv
    #
    chash
    cfv
    #
    cL
    c2
    cmin
    co
    #
    wceq
    #
    cG
    @128
    cgsu
    co
    #
    @20
    wceq
    #
    wa
    #
    vy
    @10
    wrex
    #
    wn
    @7
    @127
    wph
    @63
    @130
    wceq
    #
    @62
    wa
    #
    vx
    @10
    wrex
    @135
    psgnunilem3.in
    @137
    @134
    vx
    vy
    @10
    vx
    vy
    weq
    #
    @136
    @131
    @62
    @133
    @138
    @63
    @129
    @130
    @60
    @128
    chash
    fveq2
    eqeq1d
    @138
    @61
    @132
    @20
    @60
    @128
    cG
    cgsu
    oveq2
    eqeq1d
    anbi12d
    cbvrexv
    sylnib
    ad2antrr
    psgnunilem2
    rexlimdvaa
    a2i
    a1i
    nn0ind
    mtoi
    con2i
    exlimddv
    pm2.65i
end
