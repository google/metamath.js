include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crepr.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "crn.mm"
include "ciun.mm"
include "cn0.mm"
include "wcel.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "reprval.mm"
include "wa.mm"
include "wrex.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cmin.mm"
include "wf.mm"
include "simplr.mm"
include "elmapi.mm"
include "syl.mm"
include "ad2antrr.mm"
include "fzonn0p1.mm"
include "ffvelrnd.mm"
include "simpr.mm"
include "oveq2d.mm"
include "wb.mm"
include "opeq2.mm"
include "sneqd.mm"
include "uneq2d.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "rexeqbidv.mm"
include "cres.mm"
include "wss.mm"
include "adantr.mm"
include "fzossfzop1.mm"
include "fssresd.mm"
include "cvv.mm"
include "cn.mm"
include "nnex.mm"
include "ssexd.mm"
include "cfn.mm"
include "fzofi.mm"
include "elexi.mm"
include "elmapg.mm"
include "sylancl.mm"
include "mpbird.mm"
include "cc.mm"
include "nnsscn.mm"
include "sstrd.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "fsumcl.mm"
include "pncand.mm"
include "nfv.mm"
include "nfcv.mm"
include "wn.mm"
include "fzonel.mm"
include "sselda.mm"
include "fveq2.mm"
include "fsumsplitsn.mm"
include "cuz.mm"
include "fzosplitsn.mm"
include "nn0uz.mm"
include "eleq2s.mm"
include "sumeq1d.mm"
include "fvresd.mm"
include "sumeq2dv.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "eqtr3d.mm"
include "jca.mm"
include "fveq1.mm"
include "sumeq2sdv.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylibr.mm"
include "cz.mm"
include "nnssz.mm"
include "syl6ss.mm"
include "zsubcld.mm"
include "eleqtrrd.mm"
include "uneq1d.mm"
include "cdif.mm"
include "wfn.mm"
include "ffnd.mm"
include "fnsnsplit.mm"
include "syl2anc.mm"
include "syl6eleq.mm"
include "fzodif2.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "anasss.mm"
include "reprf.mm"
include "fsnd.mm"
include "cin.mm"
include "c0.mm"
include "fzodisjsn.mm"
include "fun2d.mm"
include "feq2d.mm"
include "ovex.mm"
include "eqeltrd.mm"
include "ad4antr.mm"
include "feq1d.mm"
include "elun1.mm"
include "ad3antrrr.mm"
include "fveq1d.mm"
include "fvun1.mm"
include "syl112anc.mm"
include "ralrimiva.mm"
include "sumeq2d.mm"
include "reprsum.mm"
include "snidg.mm"
include "fvun2.mm"
include "fvsng.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "zsscn.mm"
include "sseldi.mm"
include "eqeltrrd.mm"
include "npcand.mm"
include "r19.29ffa.mm"
include "impbida.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "elrnmpti.mm"
include "rexbii.mm"
include "syl6bbr.mm"
include "cbvrabv.mm"
include "rabeq2i.mm"
include "eliun.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem reprsuc
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cM: class M
  let vb: setvar b
  let vc: setvar c
  let va: setvar a
  let vd: setvar d
  let ve: setvar e
  let vm: setvar m
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )
  assume reprsuc.f: |- F = ( c e. ( A ( repr ` S ) ( M - b ) ) |-> ( c u. { <. S , b >. } ) )

  disjoint S b
  disjoint S c
  disjoint b c
  disjoint A b
  disjoint A c
  disjoint b c
  disjoint M b
  disjoint M c
  disjoint S b
  disjoint S c
  disjoint b ph
  disjoint c ph
  disjoint A a
  disjoint A d
  disjoint A e
  disjoint a d
  disjoint a e
  disjoint d e
  disjoint F e
  disjoint M a
  disjoint M d
  disjoint M e
  disjoint S a
  disjoint S d
  disjoint S e
  disjoint a b
  disjoint a c
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint a ph
  disjoint d ph
  disjoint e ph
  disjoint A m
  disjoint b m
  disjoint c m
  disjoint M m
  disjoint S a
  disjoint S m
  disjoint S s
  disjoint a b
  disjoint a c
  disjoint a m
  disjoint a s
  disjoint b s
  disjoint c s
  disjoint m s
  disjoint m ph
  disjoint ph s
  assert |- ( ph -> ( A ( repr ` ( S + 1 ) ) M ) = U_ b e. A ran F )

  proof
    wph
    cA
    cM
    cS
    c1
    caddc
    co
    #
    crepr
    cfv
    co
    cc0
    @0
    cfzo
    co
    #
    va
    cv
    #
    vc
    cv
    #
    cfv
    #
    va
    csu
    #
    cM
    wceq
    #
    vc
    cA
    @1
    cmap
    co
    #
    crab
    #
    vb
    cA
    cF
    crn
    #
    ciun
    #
    wph
    cA
    @0
    cM
    va
    vc
    reprval.a
    reprval.m
    wph
    cS
    c1
    reprval.s
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    nn0addcld
    reprval
    wph
    ve
    @8
    @10
    wph
    ve
    cv
    #
    @7
    wcel
    #
    @1
    @2
    @11
    cfv
    #
    va
    csu
    #
    cM
    wceq
    #
    wa
    #
    @11
    @9
    wcel
    #
    vb
    cA
    wrex
    #
    @11
    @8
    wcel
    @11
    @10
    wcel
    wph
    @16
    @11
    @3
    cS
    vb
    cv
    #
    cop
    #
    csn
    #
    cun
    #
    wceq
    #
    vc
    cA
    cM
    @19
    cmin
    co
    #
    cS
    crepr
    cfv
    #
    co
    #
    wrex
    #
    vb
    cA
    wrex
    #
    @18
    wph
    @16
    @28
    wph
    @12
    @15
    @28
    wph
    @12
    wa
    #
    @15
    wa
    #
    @27
    @11
    @3
    cS
    cS
    @11
    cfv
    #
    cop
    #
    csn
    #
    cun
    #
    wceq
    #
    vc
    cA
    cM
    @31
    cmin
    co
    #
    @25
    co
    #
    wrex
    vb
    @31
    cA
    @30
    @1
    cA
    cS
    @11
    @30
    @12
    @1
    cA
    @11
    wf
    #
    wph
    @12
    @15
    simplr
    @11
    cA
    @1
    elmapi
    #
    syl
    #
    @30
    cS
    cn0
    wcel
    #
    cS
    @1
    wcel
    #
    wph
    @41
    @12
    @15
    reprval.s
    ad2antrr
    #
    cS
    fzonn0p1
    #
    syl
    #
    ffvelrnd
    #
    @30
    @19
    @31
    wceq
    #
    wa
    #
    @23
    @35
    vc
    @26
    @37
    @48
    @24
    @36
    cA
    @25
    @48
    @19
    @31
    cM
    cmin
    @30
    @47
    simpr
    oveq2d
    oveq2d
    @47
    @23
    @35
    wb
    @30
    @47
    @22
    @34
    @11
    @47
    @21
    @33
    @3
    @47
    @20
    @32
    @19
    @31
    cS
    opeq2
    sneqd
    uneq2d
    eqeq2d
    adantl
    rexeqbidv
    @30
    @35
    @11
    @11
    cc0
    cS
    cfzo
    co
    #
    cres
    #
    @33
    cun
    #
    wceq
    vc
    @50
    @37
    @30
    @50
    @49
    @2
    vd
    cv
    #
    cfv
    #
    va
    csu
    #
    @36
    wceq
    #
    vd
    cA
    @49
    cmap
    co
    #
    crab
    #
    @37
    @30
    @50
    @56
    wcel
    #
    @49
    @2
    @50
    cfv
    #
    va
    csu
    #
    @36
    wceq
    #
    wa
    @50
    @57
    wcel
    @30
    @58
    @61
    @30
    @58
    @49
    cA
    @50
    wf
    #
    @29
    @62
    @15
    @29
    @1
    cA
    @49
    @11
    @12
    @38
    wph
    @39
    adantl
    #
    @29
    @41
    @49
    @1
    wss
    wph
    @41
    @12
    reprval.s
    adantr
    #
    cS
    fzossfzop1
    syl
    #
    fssresd
    #
    adantr
    wph
    @58
    @62
    wb
    #
    @12
    @15
    wph
    cA
    cvv
    wcel
    #
    @49
    cvv
    wcel
    @67
    wph
    cA
    cn
    cvv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    reprval.a
    ssexd
    #
    @49
    cfn
    cc0
    cS
    fzofi
    #
    elexi
    cA
    @49
    @50
    cvv
    cvv
    elmapg
    sylancl
    ad2antrr
    mpbird
    @30
    @60
    @31
    caddc
    co
    #
    @31
    cmin
    co
    @60
    @36
    @30
    @60
    @31
    @29
    @60
    cc
    wcel
    @15
    @29
    @49
    @59
    va
    @49
    cfn
    wcel
    #
    @29
    @70
    a1i
    #
    @29
    @2
    @49
    wcel
    #
    wa
    #
    cA
    cc
    @59
    wph
    cA
    cc
    wss
    #
    @12
    @74
    wph
    cA
    cn
    cc
    reprval.a
    cn
    cc
    wss
    wph
    nnsscn
    a1i
    sstrd
    #
    ad2antrr
    #
    @29
    @49
    cA
    @2
    @50
    @66
    ffvelrnda
    sseldd
    fsumcl
    adantr
    @29
    @31
    cc
    wcel
    @15
    @29
    cA
    cc
    @31
    wph
    @76
    @12
    @77
    adantr
    @29
    @1
    cA
    cS
    @11
    @63
    @29
    @41
    @42
    @64
    @44
    syl
    ffvelrnd
    sseldd
    #
    adantr
    pncand
    @30
    @71
    cM
    @31
    cmin
    @30
    @14
    @71
    cM
    @29
    @14
    @71
    wceq
    @15
    @29
    @49
    cS
    csn
    #
    cun
    #
    @13
    va
    csu
    #
    @49
    @13
    va
    csu
    #
    @31
    caddc
    co
    #
    @14
    @71
    @29
    @49
    cS
    @13
    @31
    va
    cn0
    @29
    va
    nfv
    va
    @31
    nfcv
    #
    @73
    @64
    cS
    @49
    wcel
    wn
    #
    @29
    cc0
    cS
    fzonel
    #
    a1i
    @75
    cA
    cc
    @13
    @78
    @75
    @1
    cA
    @2
    @11
    @29
    @38
    @74
    @63
    adantr
    @29
    @49
    @1
    @2
    @65
    sselda
    ffvelrnd
    sseldd
    @2
    cS
    @11
    fveq2
    #
    @79
    fsumsplitsn
    @29
    @1
    @81
    @13
    va
    @29
    @41
    @1
    @81
    wceq
    #
    @64
    @89
    cS
    cc0
    cuz
    cfv
    #
    cn0
    cc0
    cS
    fzosplitsn
    nn0uz
    eleq2s
    #
    syl
    sumeq1d
    @29
    @60
    @83
    @31
    caddc
    @29
    @49
    @59
    @13
    va
    @75
    @2
    @49
    @11
    @29
    @74
    simpr
    fvresd
    sumeq2dv
    oveq1d
    3eqtr4d
    adantr
    @29
    @15
    simpr
    eqtr3d
    oveq1d
    eqtr3d
    jca
    @55
    @61
    vd
    @50
    @56
    @52
    @50
    wceq
    #
    @54
    @60
    @36
    @92
    @49
    @53
    @59
    va
    @2
    @52
    @50
    fveq1
    sumeq2sdv
    eqeq1d
    elrab
    sylibr
    @30
    cA
    cS
    @36
    va
    vd
    wph
    cA
    cn
    wss
    #
    @12
    @15
    reprval.a
    ad2antrr
    @30
    cM
    @31
    wph
    cM
    cz
    wcel
    #
    @12
    @15
    reprval.m
    ad2antrr
    @30
    cA
    cz
    @31
    wph
    cA
    cz
    wss
    @12
    @15
    wph
    cA
    cn
    cz
    reprval.a
    nnssz
    syl6ss
    #
    ad2antrr
    @46
    sseldd
    zsubcld
    @43
    reprval
    eleqtrrd
    @30
    @3
    @50
    wceq
    #
    wa
    #
    @34
    @51
    @11
    @97
    @3
    @50
    @33
    @30
    @96
    simpr
    uneq1d
    eqeq2d
    @30
    @11
    @11
    @1
    @80
    cdif
    #
    cres
    #
    @33
    cun
    #
    @51
    @30
    @11
    @1
    wfn
    @42
    @11
    @100
    wceq
    @30
    @1
    cA
    @11
    @40
    ffnd
    @45
    @1
    @11
    cS
    fnsnsplit
    syl2anc
    @30
    @99
    @50
    @33
    @30
    @98
    @49
    @11
    @30
    cS
    @90
    wcel
    @98
    @49
    wceq
    @30
    cS
    cn0
    @90
    @43
    nn0uz
    syl6eleq
    cc0
    cS
    fzodif2
    syl
    reseq2d
    uneq1d
    eqtrd
    rspcedvd
    rspcedvd
    anasss
    wph
    @23
    @16
    vb
    vc
    cA
    @26
    wph
    @19
    cA
    wcel
    #
    wa
    #
    @3
    @26
    wcel
    #
    wa
    #
    @23
    wa
    #
    @12
    @15
    @105
    @11
    @22
    @7
    @104
    @23
    simpr
    #
    @104
    @22
    @7
    wcel
    #
    @23
    @104
    @107
    @1
    cA
    @22
    wf
    #
    @104
    @108
    @81
    cA
    @22
    wf
    @104
    @49
    @80
    cA
    @3
    @21
    @104
    cA
    @3
    cS
    @24
    @102
    @93
    @103
    wph
    @93
    @101
    reprval.a
    adantr
    adantr
    #
    @102
    @24
    cz
    wcel
    #
    @103
    @102
    cM
    @19
    wph
    @94
    @101
    reprval.m
    adantr
    #
    wph
    cA
    cz
    @19
    @95
    sselda
    zsubcld
    adantr
    #
    @102
    @41
    @103
    wph
    @41
    @101
    reprval.s
    adantr
    adantr
    #
    @102
    @103
    simpr
    #
    reprf
    #
    @104
    cS
    @19
    cn0
    cA
    @113
    wph
    @101
    @103
    simplr
    #
    fsnd
    #
    @49
    @80
    cin
    c0
    wceq
    #
    @104
    cc0
    cS
    fzodisjsn
    #
    a1i
    fun2d
    @104
    @1
    @81
    cA
    @22
    @104
    @41
    @89
    @113
    @91
    syl
    #
    feq2d
    mpbird
    #
    wph
    @107
    @108
    wb
    #
    @101
    @103
    wph
    @68
    @1
    cvv
    wcel
    @122
    @69
    cc0
    @0
    cfzo
    ovex
    cA
    @1
    @22
    cvv
    cvv
    elmapg
    sylancl
    ad2antrr
    mpbird
    adantr
    eqeltrd
    @105
    @14
    @82
    @84
    cM
    @105
    @1
    @81
    @13
    va
    @104
    @89
    @23
    @120
    adantr
    sumeq1d
    @105
    @49
    cS
    @13
    @31
    va
    cn0
    @105
    va
    nfv
    @85
    @72
    @105
    @70
    a1i
    @104
    @41
    @23
    @113
    adantr
    #
    @86
    @105
    @87
    a1i
    @105
    @74
    wa
    #
    cA
    cc
    @13
    wph
    @76
    @101
    @103
    @23
    @74
    @77
    ad4antr
    @124
    @1
    cA
    @2
    @11
    @105
    @38
    @74
    @105
    @38
    @108
    @104
    @108
    @23
    @121
    adantr
    @105
    @1
    cA
    @11
    @22
    @106
    feq1d
    mpbird
    #
    adantr
    @124
    @2
    @81
    @1
    @124
    @74
    @2
    @81
    wcel
    @105
    @74
    simpr
    #
    @2
    @49
    @80
    elun1
    syl
    @104
    @89
    @23
    @74
    @120
    ad2antrr
    eleqtrrd
    ffvelrnd
    sseldd
    @88
    @105
    cA
    cc
    @31
    wph
    @76
    @101
    @103
    @23
    @77
    ad3antrrr
    @105
    @1
    cA
    cS
    @11
    @125
    @105
    @41
    @42
    @123
    @44
    syl
    ffvelrnd
    sseldd
    #
    fsumsplitsn
    @105
    @84
    @24
    @19
    caddc
    co
    cM
    @105
    @83
    @24
    @31
    @19
    caddc
    @105
    @83
    @49
    @4
    va
    csu
    @24
    @105
    @49
    @13
    @4
    va
    @105
    @13
    @4
    wceq
    va
    @49
    @124
    @13
    @2
    @22
    cfv
    #
    @4
    @124
    @2
    @11
    @22
    @104
    @23
    @74
    simplr
    fveq1d
    @124
    @3
    @49
    wfn
    #
    @21
    @80
    wfn
    #
    @118
    @74
    @128
    @4
    wceq
    @104
    @129
    @23
    @74
    @104
    @49
    cA
    @3
    @115
    ffnd
    #
    ad2antrr
    @104
    @130
    @23
    @74
    @104
    @80
    cA
    @21
    @117
    ffnd
    #
    ad2antrr
    @118
    @124
    @119
    a1i
    @126
    @49
    @80
    @3
    @21
    @2
    fvun1
    syl112anc
    eqtrd
    ralrimiva
    sumeq2d
    @105
    cA
    @3
    cS
    @24
    va
    @104
    @93
    @23
    @109
    adantr
    @104
    @110
    @23
    @112
    adantr
    @123
    @104
    @103
    @23
    @114
    adantr
    reprsum
    eqtrd
    @105
    @31
    cS
    @22
    cfv
    #
    cS
    @21
    cfv
    #
    @19
    @105
    cS
    @11
    @22
    @106
    fveq1d
    @105
    @129
    @130
    @118
    cS
    @80
    wcel
    #
    @133
    @134
    wceq
    @104
    @129
    @23
    @131
    adantr
    @104
    @130
    @23
    @132
    adantr
    @118
    @105
    @119
    a1i
    @105
    @41
    @135
    @123
    cS
    cn0
    snidg
    syl
    @49
    @80
    @3
    @21
    cS
    fvun2
    syl112anc
    @105
    @41
    @101
    @134
    @19
    wceq
    @123
    @104
    @101
    @23
    @116
    adantr
    cS
    @19
    cn0
    cA
    fvsng
    syl2anc
    3eqtrd
    #
    oveq12d
    @105
    cM
    @19
    @105
    cz
    cc
    cM
    zsscn
    @102
    @94
    @103
    @23
    @111
    ad2antrr
    sseldi
    @105
    @31
    @19
    cc
    @136
    @127
    eqeltrrd
    npcand
    eqtrd
    3eqtrd
    jca
    r19.29ffa
    impbida
    @17
    @27
    vb
    cA
    vc
    @26
    @22
    @11
    cF
    reprsuc.f
    @3
    @21
    vc
    vex
    @20
    snex
    unex
    elrnmpti
    rexbii
    syl6bbr
    @15
    ve
    @8
    @7
    @6
    @15
    vc
    ve
    @7
    @3
    @11
    wceq
    #
    @5
    @14
    cM
    @137
    @1
    @4
    @13
    va
    @2
    @3
    @11
    fveq1
    sumeq2sdv
    eqeq1d
    cbvrabv
    rabeq2i
    vb
    @11
    cA
    @9
    eliun
    3bitr4g
    eqrdv
    eqtrd
end
