include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cprod.mm"
include "cmpt.mm"
include "cdv.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "ssid.mm"
include "jctr.mm"
include "wi.mm"
include "c0.mm"
include "cun.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "prodeq1.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "sumeq1.mm"
include "difeq1.mm"
include "prodeq1d.mm"
include "sumeq2sdv.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "a1d.mm"
include "ralrimiv.mm"
include "sumeq2d.mm"
include "c1.mm"
include "cc0.mm"
include "prod0.mm"
include "mpteq2i.mm"
include "oveq2i.mm"
include "a1i.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "1cnd.mm"
include "dvmptconst.mm"
include "sum0.mm"
include "eqcomi.mm"
include "3eqtrd.mm"
include "adantr.mm"
include "wn.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1r.mm"
include "simpl.mm"
include "ssun1.mm"
include "sstr2.mm"
include "ax-mp.mm"
include "adantl.mm"
include "jca.mm"
include "mpd.mm"
include "3adant1.mm"
include "csb.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfov.mm"
include "nfeq.mm"
include "nfan.mm"
include "nfcprod1.mm"
include "nfmpt.mm"
include "nfsum.mm"
include "nfsum1.mm"
include "nfcsb1v.mm"
include "cc.mm"
include "ad2antrr.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "syl3anc.mm"
include "syl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cvv.mm"
include "vex.mm"
include "simplr.mm"
include "simpllr.mm"
include "cr.mm"
include "cpr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "sseldd.mm"
include "nf3an.mm"
include "nfim.mm"
include "eleq1.mm"
include "3anbi2d.mm"
include "eleq1d.mm"
include "chvar.mm"
include "id.mm"
include "snid.mm"
include "elun2.mm"
include "ad2antlr.mm"
include "nfel.mm"
include "csbeq1a.mm"
include "adantlr.mm"
include "csbco.mm"
include "idi.mm"
include "sylan2.mm"
include "dvmptfprodlem.mm"
include "syl21anc.mm"
include "3exp.mm"
include "findcard2s.mm"
include "sylc.mm"

theorem dvmptfprod
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  assume dvmptfprod.iph: |- F/ i ph
  assume dvmptfprod.jph: |- F/ j ph
  assume dvmptfprod.j: |- J = ( K |`t S )
  assume dvmptfprod.k: |- K = ( TopOpen ` CCfld )
  assume dvmptfprod.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptfprod.x: |- ( ph -> X e. J )
  assume dvmptfprod.i: |- ( ph -> I e. Fin )
  assume dvmptfprod.a: |- ( ( ph /\ i e. I /\ x e. X ) -> A e. CC )
  assume dvmptfprod.b: |- ( ( ph /\ i e. I /\ x e. X ) -> B e. CC )
  assume dvmptfprod.d: |- ( ( ph /\ i e. I ) -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )
  assume dvmptfprod.bc: |- ( i = j -> B = C )

  disjoint A j
  disjoint C i
  disjoint I i
  disjoint I j
  disjoint I x
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint S i
  disjoint S j
  disjoint S x
  disjoint X i
  disjoint X j
  disjoint X x
  disjoint ph x
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a b
  disjoint a c
  disjoint a j
  disjoint b c
  disjoint b j
  disjoint c j
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint a i
  disjoint b i
  disjoint c i
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint k x
  assert |- ( ph -> ( S _D ( x e. X |-> prod_ i e. I A ) ) = ( x e. X |-> sum_ j e. I ( C x. prod_ i e. ( I \ { j } ) A ) ) )

  proof
    wph
    cI
    cfn
    wcel
    #
    wph
    cI
    cI
    wss
    #
    wa
    #
    cS
    vx
    cX
    cI
    cA
    vi
    cprod
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    cI
    cC
    cI
    vj
    cv
    #
    csn
    #
    cdif
    #
    cA
    vi
    cprod
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    wceq
    #
    dvmptfprod.i
    wph
    @1
    cI
    ssid
    jctr
    wph
    va
    cv
    #
    cI
    wss
    #
    wa
    #
    cS
    vx
    cX
    @14
    cA
    vi
    cprod
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    @14
    cC
    @14
    @7
    cdif
    #
    cA
    vi
    cprod
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    wceq
    #
    wi
    wph
    c0
    cI
    wss
    #
    wa
    #
    cS
    vx
    cX
    c0
    cA
    vi
    cprod
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    c0
    cC
    c0
    @7
    cdif
    #
    cA
    vi
    cprod
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    wceq
    #
    wi
    wph
    vb
    cv
    #
    cI
    wss
    #
    wa
    #
    cS
    vx
    cX
    @37
    cA
    vi
    cprod
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    @37
    cC
    @37
    @7
    cdif
    #
    cA
    vi
    cprod
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wph
    @37
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
    wa
    #
    cS
    vx
    cX
    @52
    cA
    vi
    cprod
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    @52
    cC
    @52
    @7
    cdif
    #
    cA
    vi
    cprod
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    wceq
    #
    wi
    @2
    @13
    wi
    va
    vb
    vc
    cI
    @14
    c0
    wceq
    #
    @16
    @27
    @25
    @36
    @64
    @15
    @26
    wph
    @14
    c0
    cI
    sseq1
    anbi2d
    @64
    @19
    @30
    @24
    @35
    @64
    @18
    @29
    cS
    cdv
    @64
    vx
    cX
    @17
    @28
    @14
    c0
    cA
    vi
    prodeq1
    mpteq2dv
    oveq2d
    @64
    vx
    cX
    @23
    @34
    @64
    @23
    c0
    @22
    vj
    csu
    @34
    @14
    c0
    @22
    vj
    sumeq1
    @64
    c0
    @22
    @33
    vj
    @64
    @21
    @32
    cC
    cmul
    @64
    @20
    @31
    cA
    vi
    @14
    c0
    @7
    difeq1
    prodeq1d
    oveq2d
    sumeq2sdv
    eqtrd
    mpteq2dv
    eqeq12d
    imbi12d
    @14
    @37
    wceq
    #
    @16
    @39
    @25
    @48
    @65
    @15
    @38
    wph
    @14
    @37
    cI
    sseq1
    anbi2d
    @65
    @19
    @42
    @24
    @47
    @65
    @18
    @41
    cS
    cdv
    @65
    vx
    cX
    @17
    @40
    @14
    @37
    cA
    vi
    prodeq1
    mpteq2dv
    oveq2d
    @65
    vx
    cX
    @23
    @46
    @65
    @23
    @37
    @22
    vj
    csu
    @46
    @14
    @37
    @22
    vj
    sumeq1
    @65
    @37
    @22
    @45
    vj
    @65
    @21
    @44
    cC
    cmul
    @65
    @20
    @43
    cA
    vi
    @14
    @37
    @7
    difeq1
    prodeq1d
    oveq2d
    sumeq2sdv
    eqtrd
    mpteq2dv
    eqeq12d
    imbi12d
    @14
    @52
    wceq
    #
    @16
    @54
    @25
    @63
    @66
    @15
    @53
    wph
    @14
    @52
    cI
    sseq1
    anbi2d
    @66
    @19
    @57
    @24
    @62
    @66
    @18
    @56
    cS
    cdv
    @66
    vx
    cX
    @17
    @55
    @14
    @52
    cA
    vi
    prodeq1
    mpteq2dv
    oveq2d
    @66
    vx
    cX
    @23
    @61
    @66
    @23
    @52
    @22
    vj
    csu
    @61
    @14
    @52
    @22
    vj
    sumeq1
    @66
    @52
    @22
    @60
    vj
    @66
    @21
    @59
    cC
    cmul
    @66
    @20
    @58
    cA
    vi
    @14
    @52
    @7
    difeq1
    prodeq1d
    oveq2d
    sumeq2sdv
    eqtrd
    mpteq2dv
    eqeq12d
    imbi12d
    @14
    cI
    wceq
    #
    @16
    @2
    @25
    @13
    @67
    @15
    @1
    wph
    @14
    cI
    cI
    sseq1
    anbi2d
    @67
    @19
    @5
    @24
    @12
    @67
    @18
    @4
    cS
    cdv
    @67
    vx
    cX
    @17
    @3
    @14
    cI
    cA
    vi
    prodeq1
    mpteq2dv
    oveq2d
    @67
    vx
    cX
    @23
    @11
    @67
    @23
    cI
    @22
    vj
    csu
    @11
    @14
    cI
    @22
    vj
    sumeq1
    @67
    cI
    @22
    @10
    vj
    @67
    @22
    @10
    wceq
    #
    vj
    cI
    @67
    @68
    @6
    cI
    wcel
    #
    @67
    @21
    @9
    cC
    cmul
    @67
    @20
    @8
    cA
    vi
    @14
    cI
    @7
    difeq1
    prodeq1d
    oveq2d
    a1d
    ralrimiv
    sumeq2d
    eqtrd
    mpteq2dv
    eqeq12d
    imbi12d
    wph
    @36
    @26
    wph
    @30
    cS
    vx
    cX
    c1
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    cc0
    cmpt
    #
    @35
    @30
    @71
    wceq
    wph
    @29
    @70
    cS
    cdv
    vx
    cX
    @28
    c1
    cA
    vi
    prod0
    mpteq2i
    oveq2i
    a1i
    wph
    vx
    cX
    c1
    cS
    dvmptfprod.s
    wph
    cX
    cJ
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    dvmptfprod.x
    cJ
    cK
    cS
    crest
    co
    @74
    dvmptfprod.j
    cK
    @73
    cS
    crest
    dvmptfprod.k
    oveq1i
    eqtri
    syl6eleq
    wph
    1cnd
    dvmptconst
    @72
    @35
    wceq
    wph
    vx
    cX
    cc0
    @34
    @34
    cc0
    @33
    vj
    sum0
    eqcomi
    mpteq2i
    a1i
    3eqtrd
    adantr
    @37
    cfn
    wcel
    #
    @50
    @37
    wcel
    wn
    #
    wa
    #
    @49
    @54
    @63
    @77
    @49
    @54
    w3a
    @54
    @76
    @48
    @63
    @77
    @49
    @54
    simp3
    @75
    @76
    @49
    @54
    simp1r
    @49
    @54
    @48
    @77
    @49
    @54
    wa
    @39
    @48
    @54
    @39
    @49
    @54
    wph
    @38
    wph
    @53
    simpl
    #
    @53
    @38
    wph
    @37
    @52
    wss
    @53
    @38
    wi
    @37
    @51
    ssun1
    @37
    @52
    cI
    sstr2
    ax-mp
    adantl
    #
    jca
    adantl
    @49
    @54
    simpl
    mpd
    3adant1
    @54
    @76
    wa
    #
    @48
    wa
    #
    vx
    cA
    cC
    @37
    cS
    vi
    vj
    @50
    vi
    @50
    cA
    csb
    #
    vj
    @50
    cC
    csb
    #
    cI
    cX
    @80
    @48
    vx
    @80
    vx
    nfv
    vx
    @42
    @47
    vx
    cS
    @41
    cdv
    vx
    cS
    nfcv
    vx
    cdv
    nfcv
    vx
    cX
    @40
    nfmpt1
    nfov
    vx
    cX
    @46
    nfmpt1
    nfeq
    nfan
    @80
    @48
    vi
    @54
    @76
    vi
    wph
    @53
    vi
    dvmptfprod.iph
    @53
    vi
    nfv
    nfan
    @76
    vi
    nfv
    nfan
    vi
    @42
    @47
    vi
    cS
    @41
    cdv
    vi
    cS
    nfcv
    #
    vi
    cdv
    nfcv
    #
    vi
    vx
    cX
    @40
    vi
    cX
    nfcv
    #
    @37
    cA
    vi
    vi
    @37
    nfcv
    #
    nfcprod1
    nfmpt
    nfov
    vi
    vx
    cX
    @46
    @86
    vi
    @37
    @45
    vj
    @87
    vi
    cC
    @44
    cmul
    vi
    cC
    nfcv
    vi
    cmul
    nfcv
    @43
    cA
    vi
    vi
    @43
    nfcv
    nfcprod1
    nfov
    nfsum
    nfmpt
    nfeq
    nfan
    @80
    @48
    vj
    @54
    @76
    vj
    wph
    @53
    vj
    dvmptfprod.jph
    @53
    vj
    nfv
    nfan
    @76
    vj
    nfv
    nfan
    vj
    @42
    @47
    vj
    @42
    nfcv
    vj
    vx
    cX
    @46
    vj
    cX
    nfcv
    #
    @37
    @45
    vj
    vj
    @37
    nfcv
    nfsum1
    nfmpt
    nfeq
    nfan
    vi
    @50
    cA
    nfcsb1v
    vj
    @50
    cC
    nfcsb1v
    #
    @81
    vi
    cv
    #
    cI
    wcel
    #
    vx
    cv
    cX
    wcel
    #
    w3a
    wph
    @91
    @92
    cA
    cc
    wcel
    @81
    @91
    wph
    @92
    @54
    wph
    @76
    @48
    @78
    ad2antrr
    #
    3ad2ant1
    @81
    @91
    @92
    simp2
    @81
    @91
    @92
    simp3
    dvmptfprod.a
    syl3anc
    @81
    @0
    @38
    @75
    @81
    wph
    @0
    @93
    dvmptfprod.i
    syl
    @54
    @38
    @76
    @48
    @79
    ad2antrr
    #
    cI
    @37
    ssfi
    syl2anc
    @50
    cvv
    wcel
    @81
    vc
    vex
    #
    a1i
    @54
    @76
    @48
    simplr
    wph
    @53
    @76
    @48
    simpllr
    wph
    cS
    cr
    cc
    cpr
    wcel
    @53
    @76
    @48
    dvmptfprod.s
    ad3antrrr
    @81
    @92
    wa
    #
    @6
    @37
    wcel
    #
    wa
    #
    wph
    @69
    @92
    cC
    cc
    wcel
    #
    @81
    wph
    @92
    @97
    @93
    ad2antrr
    @98
    @37
    cI
    @6
    @81
    @38
    @92
    @97
    @94
    ad2antrr
    @96
    @97
    simpr
    sseldd
    @81
    @92
    @97
    simplr
    wph
    @91
    @92
    w3a
    #
    cB
    cc
    wcel
    #
    wi
    wph
    @69
    @92
    w3a
    #
    @99
    wi
    #
    vi
    vj
    @102
    @99
    vi
    wph
    @69
    @92
    vi
    dvmptfprod.iph
    @69
    vi
    nfv
    #
    @92
    vi
    nfv
    nf3an
    @99
    vi
    nfv
    nfim
    @90
    @6
    wceq
    #
    @100
    @102
    @101
    @99
    @105
    @91
    @69
    wph
    @92
    @90
    @6
    cI
    eleq1
    #
    3anbi2d
    @105
    cB
    cC
    cc
    dvmptfprod.bc
    eleq1d
    imbi12d
    dvmptfprod.b
    chvar
    #
    syl3anc
    @80
    @48
    simpr
    @80
    @92
    @83
    cc
    wcel
    #
    @48
    @54
    @92
    @108
    @76
    @54
    @92
    wa
    wph
    @50
    cI
    wcel
    #
    @92
    @108
    @54
    wph
    @92
    @78
    adantr
    @53
    @109
    wph
    @92
    @53
    @52
    cI
    @50
    @53
    id
    @50
    @52
    wcel
    #
    @53
    @50
    @51
    wcel
    @110
    @50
    @95
    snid
    @50
    @51
    @37
    elun2
    ax-mp
    a1i
    sseldd
    #
    ad2antlr
    @54
    @92
    simpr
    @103
    wph
    @109
    @92
    w3a
    #
    @108
    wi
    vj
    vc
    @112
    @108
    vj
    wph
    @109
    @92
    vj
    dvmptfprod.jph
    @109
    vj
    nfv
    #
    @92
    vj
    nfv
    nf3an
    vj
    @83
    cc
    @89
    vj
    cc
    nfcv
    nfel
    nfim
    @6
    @50
    wceq
    #
    @102
    @112
    @99
    @108
    @114
    @69
    @109
    wph
    @92
    @6
    @50
    cI
    eleq1
    #
    3anbi2d
    @114
    cC
    @83
    cc
    vj
    @50
    cC
    csbeq1a
    #
    eleq1d
    imbi12d
    @107
    chvar
    syl3anc
    adantlr
    adantlr
    @54
    cS
    vx
    cX
    @82
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    @83
    cmpt
    #
    wceq
    #
    @76
    @48
    @53
    wph
    @109
    @120
    @111
    wph
    @69
    wa
    #
    cS
    vx
    cX
    vi
    @6
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
    cC
    cmpt
    #
    wceq
    #
    wi
    #
    wph
    @109
    wa
    #
    @120
    wi
    vj
    vc
    @128
    @120
    vj
    wph
    @109
    vj
    dvmptfprod.jph
    @113
    nfan
    vj
    @118
    @119
    vj
    @118
    nfcv
    vj
    vx
    cX
    @83
    @88
    @89
    nfmpt
    nfeq
    nfim
    @114
    @121
    @128
    @126
    @120
    @114
    @69
    @109
    wph
    @115
    anbi2d
    @114
    @124
    @118
    @125
    @119
    @114
    @123
    @117
    cS
    cdv
    @114
    vx
    cX
    @122
    @82
    @114
    @122
    vj
    @50
    @122
    csb
    #
    @82
    vj
    @50
    @122
    csbeq1a
    @129
    @82
    wceq
    @114
    vi
    vj
    @50
    cA
    csbco
    a1i
    eqtrd
    mpteq2dv
    oveq2d
    @114
    vx
    cX
    cC
    @83
    @116
    mpteq2dv
    eqeq12d
    imbi12d
    wph
    @91
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
    @127
    vi
    vj
    @121
    @126
    vi
    wph
    @69
    vi
    dvmptfprod.iph
    @104
    nfan
    vi
    @124
    @125
    vi
    cS
    @123
    cdv
    @84
    @85
    vi
    vx
    cX
    @122
    @86
    vi
    @6
    cA
    nfcsb1v
    nfmpt
    nfov
    vi
    @125
    nfcv
    nfeq
    nfim
    @105
    @130
    @121
    @134
    @126
    @105
    @91
    @69
    wph
    @106
    anbi2d
    @105
    @132
    @124
    @133
    @125
    @105
    @131
    @123
    cS
    cdv
    @105
    vx
    cX
    cA
    @122
    vi
    @6
    cA
    csbeq1a
    mpteq2dv
    oveq2d
    @105
    vx
    cX
    cB
    cC
    @105
    cB
    cC
    wceq
    wi
    dvmptfprod.bc
    idi
    mpteq2dv
    eqeq12d
    imbi12d
    dvmptfprod.d
    chvar
    chvar
    sylan2
    ad2antrr
    vi
    @50
    cA
    csbeq1a
    @116
    dvmptfprodlem
    syl21anc
    3exp
    findcard2s
    sylc
end
