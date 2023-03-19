include "wor.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "sopo.mm"
include "ax-mp.mm"
include "poseq.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "anbi2d.mm"
include "eqeq2d.mm"
include "breq2d.mm"
include "brabg.mm"
include "bianabs.mm"
include "wb.mm"
include "ancoms.mm"
include "orbi12d.mm"
include "notbid.mm"
include "wi.mm"
include "ralinexa.mm"
include "andi.mm"
include "eqcom.mm"
include "ralbii.mm"
include "anbi1i.mm"
include "orbi2i.mm"
include "bitri.mm"
include "rexbii.mm"
include "r19.43.mm"
include "xchbinx.mm"
include "wf.mm"
include "cab.mm"
include "feq2.mm"
include "cbvrexv.mm"
include "abbii.mm"
include "eqtri.mm"
include "orderseqlem.mm"
include "sotrieq.mm"
include "mpan.mm"
include "syl2an.mm"
include "imbi2d.mm"
include "wsbc.mm"
include "vex.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "sbcie.mm"
include "imbi1i.mm"
include "tfisg.mm"
include "sylbir.mm"
include "feq1.mm"
include "elab2.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "wss.mm"
include "onss.mm"
include "ssralv.mm"
include "syl.mm"
include "ad2antlr.mm"
include "rspcv.mm"
include "a1i.mm"
include "ffvelrn.mm"
include "cdm.mm"
include "fdm.mm"
include "word.mm"
include "eloni.mm"
include "ordirr.mm"
include "eleq2.mm"
include "biimparc.mm"
include "sylan.mm"
include "ndmfv.mm"
include "eqtr2.mm"
include "biimprd.mm"
include "ex.mm"
include "3syl.mm"
include "com23.mm"
include "sylan2.mm"
include "adantlr.mm"
include "syl5.mm"
include "exp4b.mm"
include "imp32.mm"
include "syldd.mm"
include "imp.mm"
include "mtoi.mm"
include "syld.mm"
include "ad2antrr.mm"
include "eqtr.mm"
include "biimpd.mm"
include "expcom.mm"
include "adantll.mm"
include "jcad.mm"
include "ordtri3or.mm"
include "adantr.mm"
include "3orel13.mm"
include "syl6ci.mm"
include "wfn.mm"
include "ffn.mm"
include "eqfnfv2.mm"
include "adantl.mm"
include "sylibrd.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "sylbird.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "orrd.mm"
include "3orcomb.mm"
include "df-3or.mm"
include "bitr2i.mm"
include "sylib.mm"
include "rgen2a.mm"
include "df-so.mm"
include "mpbir2an.mm"

theorem soseq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let vq: setvar q
  assume soseq.1: |- R Or ( A u. { (/) } )
  assume soseq.2: |- F = { f | E. x e. On f : x --> A }
  assume soseq.3: |- S = { <. f , g >. | ( ( f e. F /\ g e. F ) /\ E. x e. On ( A. y e. x ( f ` y ) = ( g ` y ) /\ ( f ` x ) R ( g ` x ) ) ) }
  assume soseq.4: |- -. (/) e. A

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint A y
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint f g
  disjoint g x
  disjoint f y
  disjoint g y
  disjoint x y
  disjoint R f
  disjoint R g
  disjoint R x
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a y
  disjoint b p
  disjoint b q
  disjoint b y
  disjoint p q
  disjoint p y
  disjoint q y
  disjoint A p
  disjoint A q
  disjoint f p
  disjoint f q
  disjoint p x
  disjoint q x
  disjoint F a
  disjoint F b
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint S a
  disjoint S b
  assert |- S Or F

  proof
    cF
    cS
    wor
    cF
    cS
    wpo
    va
    cv
    #
    vb
    cv
    #
    cS
    wbr
    #
    va
    vb
    weq
    #
    @1
    @0
    cS
    wbr
    #
    w3o
    #
    vb
    cF
    wral
    va
    cF
    wral
    vx
    vy
    cA
    cR
    cS
    vf
    vg
    cF
    cA
    c0
    csn
    cun
    #
    cR
    wor
    #
    @6
    cR
    wpo
    soseq.1
    @6
    cR
    sopo
    ax-mp
    soseq.2
    soseq.3
    poseq
    @5
    va
    vb
    cF
    @0
    cF
    wcel
    #
    @1
    cF
    wcel
    #
    wa
    #
    @2
    @4
    wo
    #
    @3
    wo
    #
    @5
    @10
    @11
    @3
    @10
    @11
    wn
    vy
    cv
    #
    @0
    cfv
    #
    @13
    @1
    cfv
    #
    wceq
    #
    vy
    vx
    cv
    #
    wral
    #
    @17
    @0
    cfv
    #
    @17
    @1
    cfv
    #
    cR
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    @15
    @14
    wceq
    #
    vy
    @17
    wral
    #
    @20
    @19
    cR
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    wo
    #
    wn
    #
    @3
    @10
    @11
    @29
    @10
    @2
    @23
    @4
    @28
    @10
    @2
    @23
    vf
    cv
    #
    cF
    wcel
    #
    vg
    cv
    #
    cF
    wcel
    #
    wa
    #
    @13
    @31
    cfv
    #
    @13
    @33
    cfv
    #
    wceq
    #
    vy
    @17
    wral
    #
    @17
    @31
    cfv
    #
    @17
    @33
    cfv
    #
    cR
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    wa
    #
    @8
    @34
    wa
    #
    @14
    @37
    wceq
    #
    vy
    @17
    wral
    #
    @19
    @41
    cR
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    wa
    @10
    @23
    wa
    vf
    vg
    @0
    @1
    cF
    cF
    cS
    vf
    va
    weq
    #
    @35
    @46
    @44
    @51
    @52
    @32
    @8
    @34
    @31
    @0
    cF
    eleq1
    anbi1d
    @52
    @43
    @50
    vx
    con0
    @52
    @39
    @48
    @42
    @49
    @52
    @38
    @47
    vy
    @17
    @52
    @36
    @14
    @37
    @13
    @31
    @0
    fveq1
    eqeq1d
    ralbidv
    @52
    @40
    @19
    @41
    cR
    @17
    @31
    @0
    fveq1
    breq1d
    anbi12d
    rexbidv
    anbi12d
    vg
    vb
    weq
    #
    @46
    @10
    @51
    @23
    @53
    @34
    @9
    @8
    @33
    @1
    cF
    eleq1
    anbi2d
    @53
    @50
    @22
    vx
    con0
    @53
    @48
    @18
    @49
    @21
    @53
    @47
    @16
    vy
    @17
    @53
    @37
    @15
    @14
    @13
    @33
    @1
    fveq1
    eqeq2d
    ralbidv
    @53
    @41
    @20
    @19
    cR
    @17
    @33
    @1
    fveq1
    breq2d
    anbi12d
    rexbidv
    anbi12d
    soseq.3
    brabg
    bianabs
    @9
    @8
    @4
    @28
    wb
    @9
    @8
    wa
    #
    @4
    @28
    @45
    @9
    @34
    wa
    #
    @15
    @37
    wceq
    #
    vy
    @17
    wral
    #
    @20
    @41
    cR
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    wa
    @54
    @28
    wa
    vf
    vg
    @1
    @0
    cF
    cF
    cS
    vf
    vb
    weq
    #
    @35
    @55
    @44
    @60
    @61
    @32
    @9
    @34
    @31
    @1
    cF
    eleq1
    anbi1d
    @61
    @43
    @59
    vx
    con0
    @61
    @39
    @57
    @42
    @58
    @61
    @38
    @56
    vy
    @17
    @61
    @36
    @15
    @37
    @13
    @31
    @1
    fveq1
    eqeq1d
    ralbidv
    @61
    @40
    @20
    @41
    cR
    @17
    @31
    @1
    fveq1
    breq1d
    anbi12d
    rexbidv
    anbi12d
    vg
    va
    weq
    #
    @55
    @54
    @60
    @28
    @62
    @34
    @8
    @9
    @33
    @0
    cF
    eleq1
    anbi2d
    @62
    @59
    @27
    vx
    con0
    @62
    @57
    @25
    @58
    @26
    @62
    @56
    @24
    vy
    @17
    @62
    @37
    @14
    @15
    @13
    @33
    @0
    fveq1
    eqeq2d
    ralbidv
    @62
    @41
    @19
    @20
    cR
    @17
    @33
    @0
    fveq1
    breq2d
    anbi12d
    rexbidv
    anbi12d
    soseq.3
    brabg
    bianabs
    ancoms
    orbi12d
    notbid
    @30
    @18
    @21
    @26
    wo
    #
    wn
    #
    wi
    #
    vx
    con0
    wral
    #
    @10
    @3
    @66
    @18
    @63
    wa
    #
    vx
    con0
    wrex
    #
    @29
    @18
    @63
    vx
    con0
    ralinexa
    @68
    @22
    @27
    wo
    #
    vx
    con0
    wrex
    @29
    @67
    @69
    vx
    con0
    @67
    @22
    @18
    @26
    wa
    #
    wo
    @69
    @18
    @21
    @26
    andi
    @70
    @27
    @22
    @18
    @25
    @26
    @16
    @24
    vy
    @17
    @14
    @15
    eqcom
    ralbii
    anbi1i
    orbi2i
    bitri
    rexbii
    @22
    @27
    vx
    con0
    r19.43
    bitri
    xchbinx
    @10
    @66
    @18
    @19
    @20
    wceq
    #
    wi
    #
    vx
    con0
    wral
    #
    @3
    @10
    @72
    @65
    vx
    con0
    @10
    @71
    @64
    @18
    @8
    @19
    @6
    wcel
    #
    @20
    @6
    wcel
    #
    @71
    @64
    wb
    #
    @9
    vy
    cA
    vf
    cF
    @0
    @17
    cF
    @17
    cA
    @31
    wf
    #
    vx
    con0
    wrex
    #
    vf
    cab
    @13
    cA
    @31
    wf
    #
    vy
    con0
    wrex
    #
    vf
    cab
    soseq.2
    @78
    @80
    vf
    @77
    @79
    vx
    vy
    con0
    @17
    @13
    cA
    @31
    feq2
    cbvrexv
    abbii
    eqtri
    #
    orderseqlem
    vy
    cA
    vf
    cF
    @1
    @17
    @81
    orderseqlem
    @7
    @74
    @75
    wa
    @76
    soseq.1
    @6
    @19
    @20
    cR
    sotrieq
    mpan
    syl2an
    imbi2d
    ralbidv
    @73
    @71
    vx
    con0
    wral
    #
    @10
    @3
    @73
    @71
    vx
    @13
    wsbc
    #
    vy
    @17
    wral
    #
    @71
    wi
    #
    vx
    con0
    wral
    @82
    @85
    @72
    vx
    con0
    @84
    @18
    @71
    @83
    @16
    vy
    @17
    @71
    @16
    vx
    @13
    vy
    vex
    vx
    vy
    weq
    @19
    @14
    @20
    @15
    @17
    @13
    @0
    fveq2
    @17
    @13
    @1
    fveq2
    eqeq12d
    sbcie
    ralbii
    imbi1i
    ralbii
    @71
    vx
    vy
    tfisg
    sylbir
    @10
    vp
    cv
    #
    cA
    @0
    wf
    #
    vq
    cv
    #
    cA
    @1
    wf
    #
    wa
    #
    vq
    con0
    wrex
    vp
    con0
    wrex
    #
    @82
    @3
    wi
    #
    @10
    @87
    vp
    con0
    wrex
    #
    @89
    vq
    con0
    wrex
    #
    wa
    @91
    @8
    @93
    @9
    @94
    @8
    @17
    cA
    @0
    wf
    #
    vx
    con0
    wrex
    #
    @93
    @78
    @96
    vf
    @0
    cF
    va
    vex
    @52
    @77
    @95
    vx
    con0
    @17
    cA
    @31
    @0
    feq1
    rexbidv
    soseq.2
    elab2
    @95
    @87
    vx
    vp
    con0
    @17
    @86
    cA
    @0
    feq2
    cbvrexv
    bitri
    @9
    @17
    cA
    @1
    wf
    #
    vx
    con0
    wrex
    #
    @94
    @78
    @98
    vf
    @1
    cF
    vb
    vex
    @61
    @77
    @97
    vx
    con0
    @17
    cA
    @31
    @1
    feq1
    rexbidv
    soseq.2
    elab2
    @97
    @89
    vx
    vq
    con0
    @17
    @88
    cA
    @1
    feq2
    cbvrexv
    bitri
    anbi12i
    @87
    @89
    vp
    vq
    con0
    con0
    reeanv
    bitr4i
    @90
    @92
    vp
    vq
    con0
    con0
    @86
    con0
    wcel
    #
    @88
    con0
    wcel
    #
    wa
    #
    @90
    @92
    @101
    @90
    wa
    #
    @82
    vp
    vq
    weq
    #
    @71
    vx
    @86
    wral
    #
    wa
    #
    @3
    @102
    @82
    @103
    @104
    @102
    @82
    @86
    @88
    wcel
    #
    wn
    #
    @88
    @86
    wcel
    #
    wn
    #
    wa
    @106
    @103
    @108
    w3o
    #
    @103
    @102
    @82
    @107
    @109
    @102
    @82
    @71
    vx
    @88
    wral
    #
    @107
    @100
    @82
    @111
    wi
    #
    @99
    @90
    @100
    @88
    con0
    wss
    @112
    @88
    onss
    @71
    vx
    @88
    con0
    ssralv
    syl
    ad2antlr
    @102
    @111
    @107
    @102
    @111
    wa
    @106
    c0
    cA
    wcel
    #
    soseq.4
    @102
    @111
    @106
    @113
    wi
    @102
    @106
    @111
    @113
    @102
    @106
    @111
    @86
    @0
    cfv
    #
    @86
    @1
    cfv
    #
    wceq
    #
    @113
    @106
    @111
    @116
    wi
    wi
    @102
    @71
    @116
    vx
    @86
    @88
    vx
    vp
    weq
    @19
    @114
    @20
    @115
    @17
    @86
    @0
    fveq2
    @17
    @86
    @1
    fveq2
    eqeq12d
    rspcv
    a1i
    @101
    @87
    @89
    @106
    @116
    @113
    wi
    #
    wi
    @101
    @87
    @89
    @106
    @117
    @89
    @106
    wa
    @115
    cA
    wcel
    #
    @101
    @87
    wa
    @117
    @88
    cA
    @86
    @1
    ffvelrn
    @99
    @87
    @118
    @117
    wi
    #
    @100
    @87
    @99
    @0
    cdm
    #
    @86
    wceq
    #
    @119
    @86
    cA
    @0
    fdm
    @99
    @121
    wa
    #
    @116
    @118
    @113
    @122
    @86
    @120
    wcel
    #
    wn
    #
    @114
    c0
    wceq
    #
    @116
    @118
    @113
    wi
    #
    wi
    @99
    @86
    @86
    wcel
    #
    wn
    #
    @121
    @124
    @99
    @86
    word
    #
    @128
    @86
    eloni
    #
    @86
    ordirr
    syl
    @121
    @124
    @128
    @121
    @123
    @127
    @120
    @86
    @86
    eleq2
    notbid
    biimparc
    sylan
    @86
    @0
    ndmfv
    @125
    @116
    @126
    @125
    @116
    wa
    c0
    @115
    wceq
    #
    @126
    @114
    c0
    @115
    eqtr2
    @131
    @113
    @118
    c0
    @115
    cA
    eleq1
    biimprd
    syl
    ex
    3syl
    com23
    sylan2
    adantlr
    syl5
    exp4b
    imp32
    syldd
    com23
    imp
    mtoi
    ex
    syld
    @102
    @82
    @104
    @109
    @99
    @82
    @104
    wi
    #
    @100
    @90
    @99
    @86
    con0
    wss
    @132
    @86
    onss
    @71
    vx
    @86
    con0
    ssralv
    syl
    ad2antrr
    #
    @102
    @104
    @109
    @102
    @104
    wa
    @108
    @113
    soseq.4
    @102
    @104
    @108
    @113
    wi
    @102
    @108
    @104
    @113
    @102
    @108
    @104
    @88
    @0
    cfv
    #
    @88
    @1
    cfv
    #
    wceq
    #
    @113
    @108
    @104
    @136
    wi
    wi
    @102
    @71
    @136
    vx
    @88
    @86
    vx
    vq
    weq
    @19
    @134
    @20
    @135
    @17
    @88
    @0
    fveq2
    @17
    @88
    @1
    fveq2
    eqeq12d
    rspcv
    a1i
    @101
    @87
    @89
    @108
    @136
    @113
    wi
    #
    wi
    #
    @101
    @89
    @87
    @138
    @101
    @89
    @87
    @108
    @137
    @87
    @108
    wa
    @134
    cA
    wcel
    #
    @101
    @89
    wa
    @137
    @86
    cA
    @88
    @0
    ffvelrn
    @89
    @101
    @1
    cdm
    #
    @88
    wceq
    #
    @139
    @137
    wi
    #
    @88
    cA
    @1
    fdm
    @100
    @141
    @142
    @99
    @100
    @141
    wa
    @135
    c0
    wceq
    #
    @142
    @100
    @88
    @88
    wcel
    #
    wn
    #
    @141
    @143
    @100
    @88
    word
    #
    @145
    @88
    eloni
    #
    @88
    ordirr
    syl
    @145
    @141
    wa
    @88
    @140
    wcel
    #
    wn
    #
    @143
    @141
    @149
    @145
    @141
    @148
    @144
    @140
    @88
    @88
    eleq2
    notbid
    biimparc
    @88
    @1
    ndmfv
    syl
    sylan
    @143
    @136
    @139
    @113
    @136
    @143
    @139
    @113
    wi
    #
    @136
    @143
    wa
    @134
    c0
    wceq
    #
    @150
    @134
    @135
    c0
    eqtr
    @151
    @139
    @113
    @134
    c0
    cA
    eleq1
    biimpd
    syl
    expcom
    com23
    syl
    adantll
    sylan2
    syl5
    exp4b
    com23
    imp32
    syldd
    com23
    imp
    mtoi
    ex
    syld
    jcad
    @101
    @110
    @90
    @99
    @129
    @146
    @110
    @100
    @130
    @147
    @86
    @88
    ordtri3or
    syl2an
    adantr
    @106
    @103
    @108
    3orel13
    syl6ci
    @133
    jcad
    @90
    @3
    @105
    wb
    #
    @101
    @87
    @0
    @86
    wfn
    @1
    @88
    wfn
    @152
    @89
    @86
    cA
    @0
    ffn
    @88
    cA
    @1
    ffn
    vx
    @86
    @88
    @0
    @1
    eqfnfv2
    syl2an
    adantl
    sylibrd
    ex
    rexlimivv
    sylbi
    syl5
    sylbird
    syl5bir
    sylbid
    orrd
    @5
    @2
    @4
    @3
    w3o
    @12
    @2
    @3
    @4
    3orcomb
    @2
    @4
    @3
    df-3or
    bitr2i
    sylib
    rgen2a
    va
    vb
    cF
    cS
    df-so
    mpbir2an
end
