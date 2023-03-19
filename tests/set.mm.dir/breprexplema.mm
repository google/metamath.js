include "c1.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "crepr.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "cprod.mm"
include "csu.mm"
include "cmin.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "cmul.mm"
include "cn.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "a1i.mm"
include "nn0zd.mm"
include "eqid.mm"
include "reprsuc.mm"
include "sumeq1d.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "cz.mm"
include "adantr.mm"
include "fzssz.mm"
include "simpr.mm"
include "sseldi.mm"
include "zsubcld.mm"
include "cn0.mm"
include "reprfi.mm"
include "mptfi.mm"
include "syl.mm"
include "rnfi.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "reprval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "elexd.mm"
include "wn.mm"
include "fzonel.mm"
include "actfunsnrndisj.mm"
include "cc.mm"
include "fzofi.mm"
include "wral.mm"
include "ralrimiva.mm"
include "ad3antrrr.mm"
include "wi.mm"
include "wf.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfan.mm"
include "cin.mm"
include "c0.mm"
include "simplr.mm"
include "reprf.mm"
include "fsnd.mm"
include "fzodisjsn.mm"
include "fun2.mm"
include "syl21anc.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzosplitsn.mm"
include "ad4antr.mm"
include "feq12d.mm"
include "mpbird.mm"
include "wrex.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "elrnmpti.mm"
include "sylib.mm"
include "r19.29af.mm"
include "ffvelrnd.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eleq1d.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mpd.mm"
include "fprodcl.mm"
include "anasss.mm"
include "fsumiun.mm"
include "ad2antrr.mm"
include "prodeq1d.mm"
include "wfn.mm"
include "ffn.mm"
include "fnsng.mm"
include "fvun1.mm"
include "syl112anc.mm"
include "fveq2d.mm"
include "fzossfzop1.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "eqeltrd.mm"
include "fveq12d.mm"
include "snidg.mm"
include "fvun2.mm"
include "fvsng.mm"
include "eqtrd.mm"
include "fzonn0p1.mm"
include "fprodsplitsn.mm"
include "prodeq2dv.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "sumeq2dv.mm"
include "simpl.mm"
include "actfunsnf1o.mm"
include "cvv.mm"
include "uneq1d.mm"
include "fvmptd.mm"
include "fsumf1o.mm"
include "oveq1d.mm"
include "cbvsumv.mm"
include "3eqtr4d.mm"

theorem breprexplema
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cL: class L
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vc: setvar c
  let vv: setvar v
  let vm: setvar m
  let vs: setvar s
  let vt: setvar t
  let cZ: class Z
  assume breprexp.n: |- ( ph -> N e. NN0 )
  assume breprexp.s: |- ( ph -> S e. NN0 )
  assume breprexplema.m: |- ( ph -> M e. NN0 )
  assume breprexplema.1: |- ( ph -> M <_ ( ( S + 1 ) x. N ) )
  assume breprexplema.l: |- ( ( ( ph /\ x e. ( 0 ..^ ( S + 1 ) ) ) /\ y e. NN ) -> ( ( L ` x ) ` y ) e. CC )

  disjoint L a
  disjoint L b
  disjoint L d
  disjoint L x
  disjoint L y
  disjoint a b
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint d x
  disjoint d y
  disjoint x y
  disjoint M a
  disjoint M b
  disjoint M d
  disjoint N a
  disjoint N b
  disjoint N d
  disjoint S a
  disjoint S b
  disjoint S d
  disjoint S x
  disjoint S y
  disjoint a ph
  disjoint b ph
  disjoint d ph
  disjoint ph x
  disjoint ph y
  disjoint S a
  disjoint L e
  disjoint a e
  disjoint b e
  disjoint d e
  disjoint e x
  disjoint e y
  disjoint M c
  disjoint M e
  disjoint M v
  disjoint a c
  disjoint a v
  disjoint b c
  disjoint b v
  disjoint c d
  disjoint c e
  disjoint c v
  disjoint d v
  disjoint e v
  disjoint N c
  disjoint N e
  disjoint N v
  disjoint S c
  disjoint S e
  disjoint S v
  disjoint c x
  disjoint c y
  disjoint v x
  disjoint v y
  disjoint c ph
  disjoint e ph
  disjoint ph v
  disjoint N c
  disjoint N m
  disjoint N s
  disjoint N t
  disjoint c m
  disjoint c s
  disjoint c t
  disjoint m s
  disjoint m t
  disjoint s t
  disjoint S c
  disjoint S m
  disjoint S s
  disjoint S t
  disjoint a c
  disjoint a m
  disjoint a s
  disjoint a t
  disjoint Z c
  disjoint Z m
  disjoint Z s
  disjoint Z t
  disjoint b c
  disjoint b s
  disjoint b t
  disjoint c ph
  disjoint ph s
  disjoint ph t
  assert |- ( ph -> sum_ d e. ( ( 1 ... N ) ( repr ` ( S + 1 ) ) M ) prod_ a e. ( 0 ..^ ( S + 1 ) ) ( ( L ` a ) ` ( d ` a ) ) = sum_ b e. ( 1 ... N ) sum_ d e. ( ( 1 ... N ) ( repr ` S ) ( M - b ) ) ( prod_ a e. ( 0 ..^ S ) ( ( L ` a ) ` ( d ` a ) ) x. ( ( L ` S ) ` b ) ) )

  proof
    wph
    c1
    cN
    cfz
    co
    #
    cM
    cS
    c1
    caddc
    co
    #
    crepr
    cfv
    co
    #
    cc0
    @1
    cfzo
    co
    #
    va
    cv
    #
    vd
    cv
    #
    cfv
    #
    @4
    cL
    cfv
    #
    cfv
    #
    va
    cprod
    #
    vd
    csu
    vb
    @0
    vv
    @0
    cM
    vb
    cv
    #
    cmin
    co
    #
    cS
    crepr
    cfv
    co
    #
    vv
    cv
    #
    cS
    @10
    cop
    #
    csn
    #
    cun
    #
    cmpt
    #
    crn
    #
    ciun
    #
    @9
    vd
    csu
    @0
    @18
    @9
    vd
    csu
    #
    vb
    csu
    @0
    @12
    cc0
    cS
    cfzo
    co
    #
    @8
    va
    cprod
    #
    @10
    cS
    cL
    cfv
    #
    cfv
    #
    cmul
    co
    #
    vd
    csu
    #
    vb
    csu
    wph
    @2
    @19
    @9
    vd
    wph
    @0
    cS
    @17
    cM
    vb
    vv
    @0
    cn
    wss
    #
    wph
    cN
    fz1ssnn
    #
    a1i
    wph
    cM
    breprexplema.m
    nn0zd
    #
    breprexp.s
    @17
    eqid
    #
    reprsuc
    sumeq1d
    wph
    vb
    @0
    @18
    @9
    vd
    wph
    c1
    cN
    fzfid
    #
    wph
    @10
    @0
    wcel
    #
    wa
    #
    @17
    cfn
    wcel
    #
    @18
    cfn
    wcel
    @33
    @12
    cfn
    wcel
    @34
    @33
    @0
    cS
    @11
    @27
    @33
    @28
    a1i
    #
    @33
    cM
    @10
    wph
    cM
    cz
    wcel
    @32
    @29
    adantr
    @33
    @0
    cz
    @10
    c1
    cN
    fzssz
    wph
    @32
    simpr
    #
    sseldi
    zsubcld
    #
    wph
    cS
    cn0
    wcel
    #
    @32
    breprexp.s
    adantr
    #
    wph
    @0
    cfn
    wcel
    @32
    @31
    adantr
    reprfi
    #
    vv
    @12
    @16
    mptfi
    syl
    @17
    rnfi
    syl
    wph
    vv
    @12
    @21
    @0
    vb
    @17
    cS
    cn0
    @33
    @12
    @21
    @4
    vc
    cv
    cfv
    va
    csu
    @11
    wceq
    #
    vc
    @0
    @21
    cmap
    co
    #
    crab
    @42
    @33
    @0
    cS
    @11
    va
    vc
    @35
    @37
    @39
    reprval
    @41
    vc
    @42
    ssrab2
    syl6eqss
    #
    wph
    @0
    cfn
    @31
    elexd
    #
    breprexp.s
    cS
    @21
    wcel
    wn
    #
    wph
    cc0
    cS
    fzonel
    #
    a1i
    #
    @30
    actfunsnrndisj
    wph
    @32
    @5
    @18
    wcel
    #
    @9
    cc
    wcel
    @33
    @48
    wa
    #
    @3
    @8
    va
    @3
    cfn
    wcel
    @49
    cc0
    @1
    fzofi
    a1i
    @49
    @4
    @3
    wcel
    #
    wa
    #
    vy
    cv
    #
    vx
    cv
    #
    cL
    cfv
    #
    cfv
    #
    cc
    wcel
    #
    vy
    cn
    wral
    #
    vx
    @3
    wral
    #
    @8
    cc
    wcel
    #
    wph
    @58
    @32
    @48
    @50
    wph
    @57
    vx
    @3
    wph
    @53
    @3
    wcel
    wa
    @56
    vy
    cn
    breprexplema.l
    ralrimiva
    ralrimiva
    #
    ad3antrrr
    @51
    @50
    @6
    cn
    wcel
    @58
    @59
    wi
    @49
    @50
    simpr
    #
    @51
    @0
    cn
    @6
    @28
    @51
    @3
    @0
    @4
    @5
    @49
    @3
    @0
    @5
    wf
    #
    @50
    @49
    @5
    @16
    wceq
    #
    @62
    vv
    @12
    @33
    @48
    vv
    @33
    vv
    nfv
    vv
    @5
    @18
    vv
    @5
    nfcv
    vv
    @17
    vv
    @12
    @16
    nfmpt1
    nfrn
    nfel
    nfan
    @49
    @13
    @12
    wcel
    #
    wa
    #
    @63
    wa
    #
    @62
    @21
    cS
    csn
    #
    cun
    #
    @0
    @16
    wf
    #
    @66
    @21
    @0
    @13
    wf
    @67
    @0
    @15
    wf
    @21
    @67
    cin
    c0
    wceq
    #
    @69
    @66
    @0
    @13
    cS
    @11
    @27
    @66
    @28
    a1i
    @33
    @11
    cz
    wcel
    #
    @48
    @64
    @63
    @37
    ad3antrrr
    @33
    @38
    @48
    @64
    @63
    @39
    ad3antrrr
    #
    @49
    @64
    @63
    simplr
    reprf
    @66
    cS
    @10
    cn0
    @0
    @72
    @33
    @32
    @48
    @64
    @63
    @36
    ad3antrrr
    fsnd
    @70
    @66
    cc0
    cS
    fzodisjsn
    #
    a1i
    @21
    @67
    @0
    @13
    @15
    fun2
    syl21anc
    @66
    @3
    @68
    @0
    @5
    @16
    @65
    @63
    simpr
    wph
    @3
    @68
    wceq
    #
    @32
    @48
    @64
    @63
    wph
    cS
    cc0
    cuz
    cfv
    #
    wcel
    @74
    wph
    cS
    cn0
    @75
    breprexp.s
    nn0uz
    syl6eleq
    cc0
    cS
    fzosplitsn
    syl
    #
    ad4antr
    feq12d
    mpbird
    @49
    @48
    @63
    vv
    @12
    wrex
    @33
    @48
    simpr
    vv
    @12
    @16
    @5
    @17
    @30
    @13
    @15
    vv
    vex
    @14
    snex
    #
    unex
    elrnmpti
    sylib
    r19.29af
    adantr
    @61
    ffvelrnd
    sseldi
    @56
    @59
    @52
    @7
    cfv
    #
    cc
    wcel
    #
    vx
    vy
    @4
    @6
    @3
    cn
    @53
    @4
    wceq
    #
    @55
    @78
    cc
    @80
    @52
    @54
    @7
    @53
    @4
    cL
    fveq2
    fveq1d
    eleq1d
    #
    @52
    @6
    wceq
    @78
    @8
    cc
    @52
    @6
    @7
    fveq2
    eleq1d
    rspc2v
    syl2anc
    mpd
    fprodcl
    #
    anasss
    fsumiun
    wph
    @0
    @20
    @26
    vb
    @33
    @12
    @3
    @4
    ve
    cv
    #
    @15
    cun
    #
    cfv
    #
    @7
    cfv
    #
    va
    cprod
    #
    ve
    csu
    @12
    @21
    @4
    @83
    cfv
    #
    @7
    cfv
    #
    va
    cprod
    #
    @24
    cmul
    co
    #
    ve
    csu
    #
    @20
    @26
    @33
    @12
    @87
    @91
    ve
    @33
    @83
    @12
    wcel
    #
    wa
    #
    @87
    @68
    @86
    va
    cprod
    @21
    @86
    va
    cprod
    #
    cS
    @84
    cfv
    #
    @23
    cfv
    #
    cmul
    co
    @91
    @94
    @3
    @68
    @86
    va
    wph
    @74
    @32
    @93
    @76
    ad2antrr
    prodeq1d
    @94
    @21
    cS
    @86
    @97
    va
    cn0
    @94
    va
    nfv
    va
    @97
    nfcv
    @21
    cfn
    wcel
    @94
    cc0
    cS
    fzofi
    a1i
    @33
    @38
    @93
    @39
    adantr
    #
    @45
    @94
    @46
    a1i
    @94
    @4
    @21
    wcel
    #
    wa
    #
    @86
    @89
    cc
    @100
    @85
    @88
    @7
    @100
    @83
    @21
    wfn
    #
    @15
    @67
    wfn
    #
    @70
    @99
    @85
    @88
    wceq
    @94
    @101
    @99
    @94
    @21
    @0
    @83
    wf
    @101
    @94
    @0
    @83
    cS
    @11
    @27
    @94
    @28
    a1i
    @33
    @71
    @93
    @37
    adantr
    @98
    @33
    @93
    simpr
    #
    reprf
    #
    @21
    @0
    @83
    ffn
    syl
    #
    adantr
    @94
    @102
    @99
    @94
    @38
    @32
    @102
    @98
    @33
    @32
    @93
    @36
    adantr
    #
    cS
    @10
    cn0
    @0
    fnsng
    syl2anc
    #
    adantr
    @70
    @100
    @73
    a1i
    @94
    @99
    simpr
    @21
    @67
    @83
    @15
    @4
    fvun1
    syl112anc
    fveq2d
    #
    @100
    @58
    @89
    cc
    wcel
    #
    @94
    @58
    @99
    wph
    @58
    @32
    @93
    @60
    ad2antrr
    #
    adantr
    @100
    @50
    @88
    cn
    wcel
    @58
    @109
    wi
    @94
    @21
    @3
    @4
    wph
    @21
    @3
    wss
    #
    @32
    @93
    wph
    @38
    @111
    breprexp.s
    cS
    fzossfzop1
    syl
    ad2antrr
    sselda
    @100
    @0
    cn
    @88
    @28
    @94
    @21
    @0
    @4
    @83
    @104
    ffvelrnda
    sseldi
    @56
    @109
    @79
    vx
    vy
    @4
    @88
    @3
    cn
    @81
    @52
    @88
    wceq
    @78
    @89
    cc
    @52
    @88
    @7
    fveq2
    eleq1d
    rspc2v
    syl2anc
    mpd
    eqeltrd
    @4
    cS
    wceq
    @85
    @96
    @7
    @23
    @4
    cS
    cL
    fveq2
    @4
    cS
    @84
    fveq2
    fveq12d
    @94
    @97
    @24
    cc
    @94
    @96
    @10
    @23
    @94
    @96
    cS
    @15
    cfv
    #
    @10
    @94
    @101
    @102
    @70
    cS
    @67
    wcel
    #
    @96
    @112
    wceq
    @105
    @107
    @70
    @94
    @73
    a1i
    @94
    @38
    @113
    @98
    cS
    cn0
    snidg
    syl
    @21
    @67
    @83
    @15
    cS
    fvun2
    syl112anc
    @94
    @38
    @32
    @112
    @10
    wceq
    @98
    @106
    cS
    @10
    cn0
    @0
    fvsng
    syl2anc
    eqtrd
    fveq2d
    #
    @94
    @58
    @24
    cc
    wcel
    #
    @110
    @94
    cS
    @3
    wcel
    #
    @10
    cn
    wcel
    @58
    @115
    wi
    wph
    @116
    @32
    @93
    wph
    @38
    @116
    breprexp.s
    cS
    fzonn0p1
    syl
    ad2antrr
    @94
    @0
    cn
    @10
    @28
    @106
    sseldi
    @56
    @115
    @52
    @23
    cfv
    #
    cc
    wcel
    vx
    vy
    cS
    @10
    @3
    cn
    @53
    cS
    wceq
    #
    @55
    @117
    cc
    @118
    @52
    @54
    @23
    @53
    cS
    cL
    fveq2
    fveq1d
    eleq1d
    @52
    @10
    wceq
    @117
    @24
    cc
    @52
    @10
    @23
    fveq2
    eleq1d
    rspc2v
    syl2anc
    mpd
    eqeltrd
    fprodsplitsn
    @94
    @95
    @90
    @97
    @24
    cmul
    @94
    @21
    @86
    @89
    va
    @108
    prodeq2dv
    @114
    oveq12d
    3eqtrd
    sumeq2dv
    @33
    @18
    @9
    @12
    @87
    vd
    ve
    @17
    @84
    @5
    @84
    wceq
    #
    @3
    @8
    @86
    va
    @119
    @50
    wa
    #
    @6
    @85
    @7
    @120
    @4
    @5
    @84
    @119
    @50
    simpl
    fveq1d
    fveq2d
    prodeq2dv
    @40
    wph
    vv
    @12
    @21
    @0
    vb
    @17
    cS
    cn0
    @43
    @44
    breprexp.s
    @47
    @30
    actfunsnf1o
    @94
    vv
    @83
    @16
    @84
    @12
    @17
    cvv
    @17
    @17
    wceq
    @94
    @30
    a1i
    @94
    @13
    @83
    wceq
    #
    wa
    @13
    @83
    @15
    @94
    @121
    simpr
    uneq1d
    @103
    @84
    cvv
    wcel
    @94
    @83
    @15
    ve
    vex
    @77
    unex
    a1i
    fvmptd
    @82
    fsumf1o
    @26
    @92
    wceq
    @33
    @12
    @25
    @91
    vd
    ve
    @5
    @83
    wceq
    #
    @22
    @90
    @24
    cmul
    @122
    @21
    @8
    @89
    va
    @122
    @99
    wa
    #
    @6
    @88
    @7
    @123
    @4
    @5
    @83
    @122
    @99
    simpl
    fveq1d
    fveq2d
    prodeq2dv
    oveq1d
    cbvsumv
    a1i
    3eqtr4d
    sumeq2dv
    3eqtrd
end
