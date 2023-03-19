include "wss.mm"
include "csu.mm"
include "cmpt.mm"
include "cdv.mm"
include "co.mm"
include "wceq.mm"
include "ssid.mm"
include "cfn.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "sseq1.mm"
include "sumeq1.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cc0.mm"
include "cc.mm"
include "wa.mm"
include "0cnd.mm"
include "dvmptc.mm"
include "ctopon.mm"
include "cfv.mm"
include "crest.mm"
include "cnfldtopon.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "syl.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "toponss.mm"
include "syl2anc.mm"
include "dvmptres.mm"
include "sum0.mm"
include "mpteq2i.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"
include "a1d.mm"
include "wn.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "csb.mm"
include "caddc.mm"
include "cvv.mm"
include "simpll.mm"
include "ad3antrrr.mm"
include "ad2antlr.mm"
include "ssfi.mm"
include "simp-4l.mm"
include "sselda.mm"
include "simplr.mm"
include "w3a.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "chvar.mm"
include "syl3anc.mm"
include "fsumcl.mm"
include "adantlrr.mm"
include "sumex.mm"
include "a1i.mm"
include "nfcv.mm"
include "nfsum.mm"
include "sumeq2sdv.mm"
include "cbvmpt.mm"
include "eqeq12i.mm"
include "biimpi.mm"
include "ad2antll.mm"
include "simplll.mm"
include "ssun2.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "simpr.mm"
include "wral.mm"
include "3expb.mm"
include "ancom2s.mm"
include "ralrimivva.mm"
include "rspc2.mm"
include "ancoms.mm"
include "mpan9.mm"
include "syl12anc.mm"
include "ad2antrl.mm"
include "nfmpt.mm"
include "nfov.mm"
include "nfeq.mm"
include "anbi2d.mm"
include "nfcsb.mm"
include "csbeq2dv.mm"
include "3eqtr3g.mm"
include "dvmptadd.mm"
include "cin.mm"
include "simpllr.mm"
include "disjsn.mm"
include "eqidd.mm"
include "fsumsplit.mm"
include "sumsns.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "adantrr.mm"
include "3eqtr4d.mm"
include "exp32.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "adantl.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem dvmptfsum
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let vi: setvar i
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume dvmptfsum.j: |- J = ( K |`t S )
  assume dvmptfsum.k: |- K = ( TopOpen ` CCfld )
  assume dvmptfsum.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptfsum.x: |- ( ph -> X e. J )
  assume dvmptfsum.i: |- ( ph -> I e. Fin )
  assume dvmptfsum.a: |- ( ( ph /\ i e. I /\ x e. X ) -> A e. CC )
  assume dvmptfsum.b: |- ( ( ph /\ i e. I /\ x e. X ) -> B e. CC )
  assume dvmptfsum.d: |- ( ( ph /\ i e. I ) -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )

  disjoint i x
  disjoint I i
  disjoint I x
  disjoint i ph
  disjoint ph x
  disjoint S i
  disjoint S x
  disjoint X i
  disjoint X x
  disjoint a b
  disjoint a c
  disjoint A a
  disjoint b c
  disjoint A b
  disjoint A c
  disjoint a i
  disjoint a x
  disjoint I a
  disjoint b i
  disjoint b x
  disjoint I b
  disjoint c i
  disjoint c x
  disjoint I c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint X a
  disjoint X b
  disjoint X c
  assert |- ( ph -> ( S _D ( x e. X |-> sum_ i e. I A ) ) = ( x e. X |-> sum_ i e. I B ) )

  proof
    wph
    cI
    cI
    wss
    #
    cS
    vx
    cX
    cI
    cA
    vi
    csu
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    cI
    cB
    vi
    csu
    #
    cmpt
    #
    wceq
    #
    cI
    ssid
    cI
    cfn
    wcel
    #
    wph
    @0
    @6
    wi
    #
    dvmptfsum.i
    wph
    va
    cv
    #
    cI
    wss
    #
    cS
    vx
    cX
    @9
    cA
    vi
    csu
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    @9
    cB
    vi
    csu
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wi
    wph
    c0
    cI
    wss
    #
    cS
    vx
    cX
    c0
    cA
    vi
    csu
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    c0
    cB
    vi
    csu
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wi
    wph
    vb
    cv
    #
    cI
    wss
    #
    cS
    vx
    cX
    @26
    cA
    vi
    csu
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    @26
    cB
    vi
    csu
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wi
    wph
    @26
    vc
    cv
    #
    csn
    #
    cun
    #
    cI
    wss
    #
    cS
    vx
    cX
    @37
    cA
    vi
    csu
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    @37
    cB
    vi
    csu
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wi
    wph
    @8
    wi
    va
    vb
    vc
    cI
    @9
    c0
    wceq
    #
    @17
    @25
    wph
    @46
    @10
    @18
    @16
    @24
    @9
    c0
    cI
    sseq1
    @46
    @13
    @21
    @15
    @23
    @46
    @12
    @20
    cS
    cdv
    @46
    vx
    cX
    @11
    @19
    @9
    c0
    cA
    vi
    sumeq1
    mpteq2dv
    oveq2d
    @46
    vx
    cX
    @14
    @22
    @9
    c0
    cB
    vi
    sumeq1
    mpteq2dv
    eqeq12d
    imbi12d
    imbi2d
    va
    vb
    weq
    #
    @17
    @34
    wph
    @47
    @10
    @27
    @16
    @33
    @9
    @26
    cI
    sseq1
    @47
    @13
    @30
    @15
    @32
    @47
    @12
    @29
    cS
    cdv
    @47
    vx
    cX
    @11
    @28
    @9
    @26
    cA
    vi
    sumeq1
    mpteq2dv
    oveq2d
    @47
    vx
    cX
    @14
    @31
    @9
    @26
    cB
    vi
    sumeq1
    mpteq2dv
    eqeq12d
    imbi12d
    imbi2d
    @9
    @37
    wceq
    #
    @17
    @45
    wph
    @48
    @10
    @38
    @16
    @44
    @9
    @37
    cI
    sseq1
    @48
    @13
    @41
    @15
    @43
    @48
    @12
    @40
    cS
    cdv
    @48
    vx
    cX
    @11
    @39
    @9
    @37
    cA
    vi
    sumeq1
    mpteq2dv
    oveq2d
    @48
    vx
    cX
    @14
    @42
    @9
    @37
    cB
    vi
    sumeq1
    mpteq2dv
    eqeq12d
    imbi12d
    imbi2d
    @9
    cI
    wceq
    #
    @17
    @8
    wph
    @49
    @10
    @0
    @16
    @6
    @9
    cI
    cI
    sseq1
    @49
    @13
    @3
    @15
    @5
    @49
    @12
    @2
    cS
    cdv
    @49
    vx
    cX
    @11
    @1
    @9
    cI
    cA
    vi
    sumeq1
    mpteq2dv
    oveq2d
    @49
    vx
    cX
    @14
    @4
    @9
    cI
    cB
    vi
    sumeq1
    mpteq2dv
    eqeq12d
    imbi12d
    imbi2d
    wph
    @24
    @18
    wph
    cS
    vx
    cX
    cc0
    cmpt
    #
    cdv
    co
    @50
    @21
    @23
    wph
    vx
    cc0
    cc0
    cS
    cJ
    cK
    cc
    cS
    cX
    dvmptfsum.s
    wph
    vx
    cv
    #
    cS
    wcel
    wa
    0cnd
    #
    @52
    wph
    vx
    cc0
    cS
    dvmptfsum.s
    wph
    0cnd
    dvmptc
    wph
    cJ
    cS
    ctopon
    cfv
    #
    wcel
    cX
    cJ
    wcel
    cX
    cS
    wss
    wph
    cJ
    cK
    cS
    crest
    co
    #
    @53
    dvmptfsum.j
    wph
    cK
    cc
    ctopon
    cfv
    wcel
    cS
    cc
    wss
    #
    @54
    @53
    wcel
    cK
    dvmptfsum.k
    cnfldtopon
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @55
    dvmptfsum.s
    cS
    recnprss
    syl
    cS
    cK
    cc
    resttopon
    sylancr
    syl5eqel
    dvmptfsum.x
    cX
    cJ
    cS
    toponss
    syl2anc
    dvmptfsum.j
    dvmptfsum.k
    dvmptfsum.x
    dvmptres
    @20
    @50
    cS
    cdv
    vx
    cX
    @19
    cc0
    cA
    vi
    sum0
    mpteq2i
    oveq2i
    vx
    cX
    @22
    cc0
    cB
    vi
    sum0
    mpteq2i
    3eqtr4g
    a1d
    @26
    cfn
    wcel
    #
    @35
    @26
    wcel
    wn
    #
    wa
    wph
    @34
    @45
    @58
    wph
    @34
    @45
    wi
    #
    wi
    @57
    wph
    @58
    @59
    @34
    @38
    @33
    wi
    wph
    @58
    wa
    #
    @45
    @38
    @27
    @33
    @26
    @37
    wss
    @38
    @27
    @26
    @36
    ssun1
    @26
    @37
    cI
    sstr
    mpan
    #
    imim1i
    @60
    @38
    @33
    @44
    @60
    @38
    @33
    @44
    @60
    @38
    @33
    wa
    #
    wa
    #
    cS
    va
    cX
    @26
    vx
    @9
    cA
    csb
    #
    vi
    csu
    #
    vi
    @35
    @64
    csb
    #
    caddc
    co
    #
    cmpt
    #
    cdv
    co
    va
    cX
    @26
    vx
    @9
    cB
    csb
    #
    vi
    csu
    #
    vi
    @35
    @69
    csb
    #
    caddc
    co
    #
    cmpt
    #
    @41
    @43
    @63
    va
    @65
    @70
    @66
    @71
    cS
    cvv
    cc
    cX
    @63
    wph
    @56
    wph
    @58
    @62
    simpll
    #
    dvmptfsum.s
    syl
    @60
    @38
    @9
    cX
    wcel
    #
    @65
    cc
    wcel
    @33
    @60
    @38
    wa
    #
    @75
    wa
    #
    @26
    @64
    vi
    @77
    @7
    @27
    @57
    wph
    @7
    @58
    @38
    @75
    dvmptfsum.i
    ad3antrrr
    #
    @38
    @27
    @60
    @75
    @61
    ad2antlr
    #
    cI
    @26
    ssfi
    syl2anc
    @77
    vi
    cv
    #
    @26
    wcel
    #
    wa
    wph
    @80
    cI
    wcel
    #
    @75
    @64
    cc
    wcel
    #
    wph
    @58
    @38
    @75
    @81
    simp-4l
    @77
    @26
    cI
    @80
    @79
    sselda
    @76
    @75
    @81
    simplr
    wph
    @82
    @51
    cX
    wcel
    #
    w3a
    #
    cA
    cc
    wcel
    #
    wi
    wph
    @82
    @75
    w3a
    #
    @83
    wi
    vx
    va
    @87
    @83
    vx
    @87
    vx
    nfv
    #
    vx
    @64
    cc
    vx
    @9
    cA
    nfcsb1v
    #
    nfel1
    #
    nfim
    vx
    va
    weq
    #
    @85
    @87
    @86
    @83
    @91
    @84
    @75
    wph
    @82
    @51
    @9
    cX
    eleq1
    3anbi3d
    #
    @91
    cA
    @64
    cc
    vx
    @9
    cA
    csbeq1a
    #
    eleq1d
    #
    imbi12d
    dvmptfsum.a
    chvar
    #
    syl3anc
    fsumcl
    adantlrr
    @70
    cvv
    wcel
    @63
    @75
    wa
    @26
    @69
    vi
    sumex
    a1i
    @33
    cS
    va
    cX
    @65
    cmpt
    #
    cdv
    co
    #
    va
    cX
    @70
    cmpt
    #
    wceq
    #
    @60
    @38
    @33
    @99
    @30
    @97
    @32
    @98
    @29
    @96
    cS
    cdv
    vx
    va
    cX
    @28
    @65
    va
    @28
    nfcv
    vx
    @26
    @64
    vi
    vx
    @26
    nfcv
    #
    @89
    nfsum
    @91
    @26
    cA
    @64
    vi
    @93
    sumeq2sdv
    cbvmpt
    oveq2i
    vx
    va
    cX
    @31
    @70
    va
    @31
    nfcv
    vx
    @26
    @69
    vi
    @100
    vx
    @9
    cB
    nfcsb1v
    #
    nfsum
    @91
    @26
    cB
    @69
    vi
    vx
    @9
    cB
    csbeq1a
    #
    sumeq2sdv
    cbvmpt
    eqeq12i
    biimpi
    ad2antll
    @60
    @38
    @75
    @66
    cc
    wcel
    #
    @33
    @77
    wph
    @35
    cI
    wcel
    #
    @75
    @103
    wph
    @58
    @38
    @75
    simplll
    #
    @38
    @104
    @60
    @75
    @38
    @36
    cI
    wss
    #
    @104
    @36
    @37
    wss
    @38
    @106
    @36
    @26
    ssun2
    @36
    @37
    cI
    sstr
    mpan
    @35
    cI
    vc
    vex
    #
    snss
    sylibr
    #
    ad2antlr
    #
    @76
    @75
    simpr
    #
    wph
    @86
    vi
    cI
    wral
    vx
    cX
    wral
    #
    @104
    @75
    wa
    #
    @103
    wph
    @86
    vx
    vi
    cX
    cI
    wph
    @82
    @84
    @86
    wph
    @82
    @84
    @86
    dvmptfsum.a
    3expb
    ancom2s
    ralrimivva
    @75
    @104
    @111
    @103
    wi
    @86
    @103
    @83
    vx
    vi
    @9
    @35
    cX
    cI
    @90
    vi
    @66
    cc
    vi
    @35
    @64
    nfcsb1v
    nfel1
    @94
    vi
    vc
    weq
    #
    @64
    @66
    cc
    vi
    @35
    @64
    csbeq1a
    eleq1d
    rspc2
    ancoms
    mpan9
    syl12anc
    #
    adantlrr
    @60
    @38
    @75
    @71
    cc
    wcel
    #
    @33
    @77
    wph
    @104
    @75
    @115
    @105
    @109
    @110
    wph
    cB
    cc
    wcel
    #
    vi
    cI
    wral
    vx
    cX
    wral
    #
    @112
    @115
    wph
    @116
    vx
    vi
    cX
    cI
    wph
    @82
    @84
    @116
    wph
    @82
    @84
    @116
    dvmptfsum.b
    3expb
    ancom2s
    ralrimivva
    @75
    @104
    @117
    @115
    wi
    @116
    @115
    @69
    cc
    wcel
    #
    vx
    vi
    @9
    @35
    cX
    cI
    vx
    @69
    cc
    @101
    nfel1
    #
    vi
    @71
    cc
    vi
    @35
    @69
    nfcsb1v
    nfel1
    @91
    cB
    @69
    cc
    @102
    eleq1d
    #
    @113
    @69
    @71
    cc
    vi
    @35
    @69
    csbeq1a
    eleq1d
    rspc2
    ancoms
    mpan9
    syl12anc
    #
    adantlrr
    @63
    wph
    @104
    cS
    va
    cX
    @66
    cmpt
    #
    cdv
    co
    #
    va
    cX
    @71
    cmpt
    #
    wceq
    @74
    @38
    @104
    @60
    @33
    @108
    ad2antrl
    wph
    @104
    wa
    #
    cS
    vx
    cX
    vi
    @35
    cA
    csb
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    vi
    @35
    cB
    csb
    #
    cmpt
    #
    @123
    @124
    wph
    @82
    wa
    #
    cS
    vx
    cX
    cA
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    cB
    cmpt
    #
    wceq
    #
    wi
    @125
    @128
    @130
    wceq
    #
    wi
    vi
    vc
    @125
    @136
    vi
    @125
    vi
    nfv
    vi
    @128
    @130
    vi
    cS
    @127
    cdv
    vi
    cS
    nfcv
    vi
    cdv
    nfcv
    vi
    vx
    cX
    @126
    vi
    cX
    nfcv
    #
    vi
    @35
    cA
    nfcsb1v
    nfmpt
    nfov
    vi
    vx
    cX
    @129
    @137
    vi
    @35
    cB
    nfcsb1v
    nfmpt
    nfeq
    nfim
    @113
    @131
    @125
    @135
    @136
    @113
    @82
    @104
    wph
    @80
    @35
    cI
    eleq1
    anbi2d
    @113
    @133
    @128
    @134
    @130
    @113
    @132
    @127
    cS
    cdv
    @113
    vx
    cX
    cA
    @126
    vi
    @35
    cA
    csbeq1a
    mpteq2dv
    oveq2d
    @113
    vx
    cX
    cB
    @129
    vi
    @35
    cB
    csbeq1a
    mpteq2dv
    eqeq12d
    imbi12d
    dvmptfsum.d
    chvar
    @127
    @122
    cS
    cdv
    vx
    va
    cX
    @126
    @66
    va
    @126
    nfcv
    vx
    vi
    @35
    @64
    vx
    @35
    nfcv
    #
    @89
    nfcsb
    @91
    vi
    @35
    cA
    @64
    @93
    csbeq2dv
    cbvmpt
    oveq2i
    vx
    va
    cX
    @129
    @71
    va
    @129
    nfcv
    vx
    vi
    @35
    @69
    @138
    @101
    nfcsb
    @91
    vi
    @35
    cB
    @69
    @102
    csbeq2dv
    cbvmpt
    3eqtr3g
    syl2anc
    dvmptadd
    @63
    @40
    @68
    cS
    cdv
    @60
    @38
    @40
    @68
    wceq
    @33
    @76
    @40
    va
    cX
    @37
    @64
    vi
    csu
    #
    cmpt
    @68
    vx
    va
    cX
    @39
    @139
    va
    @39
    nfcv
    vx
    @37
    @64
    vi
    vx
    @37
    nfcv
    #
    @89
    nfsum
    @91
    @37
    cA
    @64
    vi
    @93
    sumeq2sdv
    cbvmpt
    @76
    va
    cX
    @139
    @67
    @77
    @139
    @65
    @36
    @64
    vi
    csu
    #
    caddc
    co
    @67
    @77
    @26
    @36
    @64
    @37
    vi
    @77
    @58
    @26
    @36
    cin
    c0
    wceq
    wph
    @58
    @38
    @75
    simpllr
    @26
    @35
    disjsn
    sylibr
    #
    @77
    @37
    eqidd
    #
    @77
    @7
    @38
    @37
    cfn
    wcel
    @78
    @60
    @38
    @75
    simplr
    #
    cI
    @37
    ssfi
    syl2anc
    #
    @77
    @80
    @37
    wcel
    #
    wa
    #
    wph
    @82
    @75
    @83
    wph
    @58
    @38
    @75
    @146
    simp-4l
    #
    @77
    @37
    cI
    @80
    @144
    sselda
    #
    @76
    @75
    @146
    simplr
    #
    @95
    syl3anc
    fsumsplit
    @77
    @141
    @66
    @65
    caddc
    @77
    @35
    cvv
    wcel
    #
    @103
    @141
    @66
    wceq
    @107
    @114
    @64
    vi
    @35
    cvv
    sumsns
    sylancr
    oveq2d
    eqtrd
    mpteq2dva
    syl5eq
    adantrr
    oveq2d
    @60
    @38
    @43
    @73
    wceq
    @33
    @76
    @43
    va
    cX
    @37
    @69
    vi
    csu
    #
    cmpt
    @73
    vx
    va
    cX
    @42
    @152
    va
    @42
    nfcv
    vx
    @37
    @69
    vi
    @140
    @101
    nfsum
    @91
    @37
    cB
    @69
    vi
    @102
    sumeq2sdv
    cbvmpt
    @76
    va
    cX
    @152
    @72
    @77
    @152
    @70
    @36
    @69
    vi
    csu
    #
    caddc
    co
    @72
    @77
    @26
    @36
    @69
    @37
    vi
    @142
    @143
    @145
    @147
    wph
    @82
    @75
    @118
    @148
    @149
    @150
    @85
    @116
    wi
    @87
    @118
    wi
    vx
    va
    @87
    @118
    vx
    @88
    @119
    nfim
    @91
    @85
    @87
    @116
    @118
    @92
    @120
    imbi12d
    dvmptfsum.b
    chvar
    syl3anc
    fsumsplit
    @77
    @153
    @71
    @70
    caddc
    @77
    @151
    @115
    @153
    @71
    wceq
    @107
    @121
    @69
    vi
    @35
    cvv
    sumsns
    sylancr
    oveq2d
    eqtrd
    mpteq2dva
    syl5eq
    adantrr
    3eqtr4d
    exp32
    a2d
    syl5
    expcom
    adantl
    a2d
    findcard2s
    mpcom
    mpi
end
