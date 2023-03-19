include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "cab.mm"
include "feq2.mm"
include "cbvrexv.mm"
include "abbii.mm"
include "eqtri.mm"
include "orderseqlem.mm"
include "poirr.mm"
include "sylancr.mm"
include "intnand.mm"
include "adantr.mm"
include "nrexdv.mm"
include "imnan.mm"
include "mpbi.mm"
include "vex.mm"
include "weq.mm"
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
include "brab.mm"
include "mtbir.mm"
include "raleq.mm"
include "fveq2.mm"
include "breq12d.mm"
include "syl5bb.mm"
include "simplll.mm"
include "simplrr.mm"
include "an4.mm"
include "2rexbii.mm"
include "reeanv.mm"
include "bitri.mm"
include "wel.mm"
include "w3o.mm"
include "word.mm"
include "eloni.mm"
include "ordtri3or.mm"
include "syl2an.mm"
include "simp1l.mm"
include "wss.mm"
include "onelss.mm"
include "imp.mm"
include "adantll.mm"
include "ssralv.mm"
include "anim2d.mm"
include "r19.26.mm"
include "syl6ibr.mm"
include "eqtr.mm"
include "ralimi.mm"
include "syl6.mm"
include "syl.mm"
include "adantrd.mm"
include "3impia.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "breq2.mm"
include "biimpd.mm"
include "com3l.mm"
include "ad2ant2lr.mm"
include "impcom.mm"
include "3adant1.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "a1d.mm"
include "3exp.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "ad2antll.mm"
include "3jca.mm"
include "potr.mm"
include "anim12i.mm"
include "anassrs.mm"
include "sylan2.mm"
include "exp32.mm"
include "imbi1d.mm"
include "syl5ibcom.mm"
include "simp1r.mm"
include "adantlr.mm"
include "anim1d.mm"
include "sylbir.mm"
include "breq1.mm"
include "biimprd.mm"
include "ad2ant2rl.mm"
include "3jaod.mm"
include "mpd.mm"
include "rexlimivv.mm"
include "jca31.mm"
include "an4s.mm"
include "syl2anb.mm"
include "sylibr.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "rgen3.mm"
include "df-po.mm"
include "mpbir.mm"

theorem poseq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let vb: setvar b
  let va: setvar a
  let vc: setvar c
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  assume poseq.1: |- R Po ( A u. { (/) } )
  assume poseq.2: |- F = { f | E. x e. On f : x --> A }
  assume poseq.3: |- S = { <. f , g >. | ( ( f e. F /\ g e. F ) /\ E. x e. On ( A. y e. x ( f ` y ) = ( g ` y ) /\ ( f ` x ) R ( g ` x ) ) ) }

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint f g
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint R f
  disjoint R g
  disjoint R x
  disjoint A b
  disjoint b f
  disjoint b x
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a t
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b g
  disjoint b t
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint c f
  disjoint c g
  disjoint c t
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint g t
  disjoint g w
  disjoint g z
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F t
  disjoint F w
  disjoint F z
  disjoint R t
  disjoint R w
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S c
  assert |- S Po F

  proof
    cF
    cS
    wpo
    va
    cv
    #
    @0
    cS
    wbr
    #
    wn
    #
    @0
    vb
    cv
    #
    cS
    wbr
    #
    @3
    vc
    cv
    #
    cS
    wbr
    #
    wa
    #
    @0
    @5
    cS
    wbr
    #
    wi
    #
    wa
    #
    vc
    cF
    wral
    vb
    cF
    wral
    va
    cF
    wral
    @10
    va
    vb
    vc
    cF
    cF
    cF
    @10
    @0
    cF
    wcel
    #
    @3
    cF
    wcel
    #
    @5
    cF
    wcel
    #
    w3a
    @2
    @9
    @1
    @11
    @11
    wa
    #
    vy
    cv
    #
    @0
    cfv
    #
    @16
    wceq
    #
    vy
    vx
    cv
    #
    wral
    #
    @18
    @0
    cfv
    #
    @20
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
    @14
    @23
    wn
    #
    wi
    @24
    wn
    @11
    @25
    @11
    @11
    @22
    vx
    con0
    @11
    @22
    wn
    @18
    con0
    wcel
    @11
    @21
    @19
    @11
    cA
    c0
    csn
    cun
    #
    cR
    wpo
    #
    @20
    @26
    wcel
    @21
    wn
    poseq.1
    vb
    cA
    vf
    cF
    @0
    @18
    cF
    @18
    cA
    vf
    cv
    #
    wf
    #
    vx
    con0
    wrex
    #
    vf
    cab
    @3
    cA
    @28
    wf
    #
    vb
    con0
    wrex
    #
    vf
    cab
    poseq.2
    @30
    @32
    vf
    @29
    @31
    vx
    vb
    con0
    @18
    @3
    cA
    @28
    feq2
    cbvrexv
    abbii
    eqtri
    orderseqlem
    @26
    @20
    cR
    poirr
    sylancr
    intnand
    adantr
    nrexdv
    adantr
    @14
    @23
    imnan
    mpbi
    @28
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
    @15
    @28
    cfv
    #
    @15
    @34
    cfv
    #
    wceq
    #
    vy
    @18
    wral
    #
    @18
    @28
    cfv
    #
    @18
    @34
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
    @11
    @35
    wa
    #
    @16
    @38
    wceq
    #
    vy
    @18
    wral
    #
    @20
    @42
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
    @24
    vf
    vg
    @0
    @0
    cS
    va
    vex
    #
    @53
    vf
    va
    weq
    #
    @36
    @47
    @45
    @52
    @54
    @33
    @11
    @35
    @28
    @0
    cF
    eleq1
    anbi1d
    #
    @54
    @44
    @51
    vx
    con0
    @54
    @40
    @49
    @43
    @50
    @54
    @39
    @48
    vy
    @18
    @54
    @37
    @16
    @38
    @15
    @28
    @0
    fveq1
    eqeq1d
    #
    ralbidv
    @54
    @41
    @20
    @42
    cR
    @18
    @28
    @0
    fveq1
    breq1d
    anbi12d
    rexbidv
    anbi12d
    vg
    va
    weq
    #
    @47
    @14
    @52
    @23
    @57
    @35
    @11
    @11
    @34
    @0
    cF
    eleq1
    anbi2d
    @57
    @51
    @22
    vx
    con0
    @57
    @49
    @19
    @50
    @21
    @57
    @48
    @17
    vy
    @18
    @57
    @38
    @16
    @16
    @15
    @34
    @0
    fveq1
    eqeq2d
    ralbidv
    @57
    @42
    @20
    @20
    cR
    @18
    @34
    @0
    fveq1
    breq2d
    anbi12d
    rexbidv
    anbi12d
    poseq.3
    brab
    mtbir
    @7
    @11
    @13
    wa
    #
    @16
    @15
    @5
    cfv
    #
    wceq
    #
    vy
    vt
    cv
    #
    wral
    #
    @61
    @0
    cfv
    #
    @61
    @5
    cfv
    #
    cR
    wbr
    #
    wa
    #
    vt
    con0
    wrex
    #
    wa
    #
    @8
    @4
    @11
    @12
    wa
    #
    @16
    @15
    @3
    cfv
    #
    wceq
    #
    vy
    vz
    cv
    #
    wral
    #
    @72
    @0
    cfv
    #
    @72
    @3
    cfv
    #
    cR
    wbr
    #
    wa
    #
    vz
    con0
    wrex
    #
    wa
    #
    @12
    @13
    wa
    #
    @70
    @59
    wceq
    #
    vy
    vw
    cv
    #
    wral
    #
    @82
    @3
    cfv
    #
    @82
    @5
    cfv
    #
    cR
    wbr
    #
    wa
    #
    vw
    con0
    wrex
    #
    wa
    #
    @68
    @6
    @46
    @47
    @48
    vy
    @72
    wral
    #
    @74
    @72
    @34
    cfv
    #
    cR
    wbr
    #
    wa
    #
    vz
    con0
    wrex
    #
    wa
    @79
    vf
    vg
    @0
    @3
    cS
    @53
    vb
    vex
    #
    @54
    @36
    @47
    @45
    @94
    @55
    @45
    @39
    vy
    @72
    wral
    #
    @72
    @28
    cfv
    #
    @91
    cR
    wbr
    #
    wa
    #
    vz
    con0
    wrex
    @54
    @94
    @44
    @99
    vx
    vz
    con0
    vx
    vz
    weq
    #
    @40
    @96
    @43
    @98
    @39
    vy
    @18
    @72
    raleq
    @100
    @41
    @97
    @42
    @91
    cR
    @18
    @72
    @28
    fveq2
    @18
    @72
    @34
    fveq2
    breq12d
    anbi12d
    cbvrexv
    @54
    @99
    @93
    vz
    con0
    @54
    @96
    @90
    @98
    @92
    @54
    @39
    @48
    vy
    @72
    @56
    ralbidv
    @54
    @97
    @74
    @91
    cR
    @72
    @28
    @0
    fveq1
    breq1d
    anbi12d
    rexbidv
    syl5bb
    anbi12d
    vg
    vb
    weq
    #
    @47
    @69
    @94
    @78
    @101
    @35
    @12
    @11
    @34
    @3
    cF
    eleq1
    anbi2d
    @101
    @93
    @77
    vz
    con0
    @101
    @90
    @73
    @92
    @76
    @101
    @48
    @71
    vy
    @72
    @101
    @38
    @70
    @16
    @15
    @34
    @3
    fveq1
    eqeq2d
    ralbidv
    @101
    @91
    @75
    @74
    cR
    @72
    @34
    @3
    fveq1
    breq2d
    anbi12d
    rexbidv
    anbi12d
    poseq.3
    brab
    @46
    @12
    @35
    wa
    #
    @70
    @38
    wceq
    #
    vy
    @82
    wral
    #
    @84
    @82
    @34
    cfv
    #
    cR
    wbr
    #
    wa
    #
    vw
    con0
    wrex
    #
    wa
    @89
    vf
    vg
    @3
    @5
    cS
    @95
    vc
    vex
    #
    vf
    vb
    weq
    #
    @36
    @102
    @45
    @108
    @110
    @33
    @12
    @35
    @28
    @3
    cF
    eleq1
    anbi1d
    @45
    @39
    vy
    @82
    wral
    #
    @82
    @28
    cfv
    #
    @105
    cR
    wbr
    #
    wa
    #
    vw
    con0
    wrex
    @110
    @108
    @44
    @114
    vx
    vw
    con0
    vx
    vw
    weq
    #
    @40
    @111
    @43
    @113
    @39
    vy
    @18
    @82
    raleq
    @115
    @41
    @112
    @42
    @105
    cR
    @18
    @82
    @28
    fveq2
    @18
    @82
    @34
    fveq2
    breq12d
    anbi12d
    cbvrexv
    @110
    @114
    @107
    vw
    con0
    @110
    @111
    @104
    @113
    @106
    @110
    @39
    @103
    vy
    @82
    @110
    @37
    @70
    @38
    @15
    @28
    @3
    fveq1
    eqeq1d
    ralbidv
    @110
    @112
    @84
    @105
    cR
    @82
    @28
    @3
    fveq1
    breq1d
    anbi12d
    rexbidv
    syl5bb
    anbi12d
    vg
    vc
    weq
    #
    @102
    @80
    @108
    @88
    @116
    @35
    @13
    @12
    @34
    @5
    cF
    eleq1
    #
    anbi2d
    @116
    @107
    @87
    vw
    con0
    @116
    @104
    @83
    @106
    @86
    @116
    @103
    @81
    vy
    @82
    @116
    @38
    @59
    @70
    @15
    @34
    @5
    fveq1
    #
    eqeq2d
    ralbidv
    @116
    @105
    @85
    @84
    cR
    @82
    @34
    @5
    fveq1
    breq2d
    anbi12d
    rexbidv
    anbi12d
    poseq.3
    brab
    @69
    @80
    @78
    @88
    @68
    @69
    @80
    wa
    #
    @78
    @88
    wa
    #
    wa
    @11
    @13
    @67
    @11
    @12
    @80
    @120
    simplll
    @69
    @12
    @13
    @120
    simplrr
    @120
    @119
    @67
    @120
    @73
    @83
    wa
    #
    @76
    @86
    wa
    #
    wa
    #
    vw
    con0
    wrex
    vz
    con0
    wrex
    #
    @119
    @67
    wi
    #
    @124
    @77
    @87
    wa
    #
    vw
    con0
    wrex
    vz
    con0
    wrex
    @120
    @123
    @126
    vz
    vw
    con0
    con0
    @73
    @83
    @76
    @86
    an4
    2rexbii
    @77
    @87
    vz
    vw
    con0
    con0
    reeanv
    bitri
    @123
    @125
    vz
    vw
    con0
    con0
    @72
    con0
    wcel
    #
    @82
    con0
    wcel
    #
    wa
    #
    vz
    vw
    wel
    #
    vz
    vw
    weq
    #
    vw
    vz
    wel
    #
    w3o
    #
    @123
    @125
    wi
    #
    @127
    @72
    word
    @82
    word
    @133
    @128
    @72
    eloni
    @82
    eloni
    @72
    @82
    ordtri3or
    syl2an
    @129
    @130
    @134
    @131
    @132
    @129
    @130
    @123
    @125
    @129
    @130
    @123
    w3a
    #
    @67
    @119
    @135
    @127
    @60
    vy
    @72
    wral
    #
    @74
    @72
    @5
    cfv
    #
    cR
    wbr
    #
    @67
    @127
    @128
    @130
    @123
    simp1l
    @129
    @130
    @123
    @136
    @129
    @130
    wa
    #
    @121
    @136
    @122
    @139
    @72
    @82
    wss
    #
    @121
    @136
    wi
    @128
    @130
    @140
    @127
    @128
    @130
    @140
    @82
    @72
    onelss
    imp
    adantll
    @140
    @121
    @71
    @81
    wa
    #
    vy
    @72
    wral
    #
    @136
    @140
    @121
    @73
    @81
    vy
    @72
    wral
    #
    wa
    #
    @142
    @140
    @83
    @143
    @73
    @81
    vy
    @72
    @82
    ssralv
    anim2d
    @71
    @81
    vy
    @72
    r19.26
    #
    syl6ibr
    @141
    @60
    vy
    @72
    @16
    @70
    @59
    eqtr
    #
    ralimi
    #
    syl6
    syl
    adantrd
    3impia
    @130
    @123
    @138
    @129
    @123
    @130
    @138
    @83
    @76
    @130
    @138
    wi
    #
    @73
    @86
    @83
    @76
    @148
    @130
    @83
    @76
    @138
    @130
    @83
    @75
    @137
    wceq
    #
    @76
    @138
    wi
    @81
    @149
    vy
    @72
    @82
    vy
    vz
    weq
    @70
    @75
    @59
    @137
    @15
    @72
    @3
    fveq2
    @15
    @72
    @5
    fveq2
    eqeq12d
    rspcv
    @149
    @76
    @138
    @75
    @137
    @74
    cR
    breq2
    biimpd
    syl6
    com3l
    imp
    ad2ant2lr
    impcom
    3adant1
    @66
    @136
    @138
    wa
    #
    vt
    @72
    con0
    vt
    vz
    weq
    #
    @62
    @136
    @65
    @138
    @60
    vy
    @61
    @72
    raleq
    @151
    @63
    @74
    @64
    @137
    cR
    @61
    @72
    @0
    fveq2
    @61
    @72
    @5
    fveq2
    breq12d
    anbi12d
    rspcev
    #
    syl12anc
    a1d
    3exp
    @127
    @131
    @134
    wi
    @128
    @127
    @142
    @76
    @75
    @137
    cR
    wbr
    #
    wa
    #
    wa
    #
    @125
    wi
    @131
    @134
    @127
    @155
    @119
    @67
    @155
    @119
    wa
    @127
    @150
    @67
    @142
    @154
    @119
    @150
    @142
    @136
    @154
    @119
    wa
    @138
    @147
    @119
    @154
    @138
    @119
    @27
    @74
    @26
    wcel
    #
    @75
    @26
    wcel
    #
    @137
    @26
    wcel
    #
    w3a
    @154
    @138
    wi
    poseq.1
    @119
    @156
    @157
    @158
    @11
    @156
    @12
    @80
    vx
    cA
    vf
    cF
    @0
    @72
    poseq.2
    orderseqlem
    ad2antrr
    @12
    @157
    @11
    @80
    vx
    cA
    vf
    cF
    @3
    @72
    poseq.2
    orderseqlem
    ad2antlr
    @13
    @158
    @69
    @12
    vx
    cA
    vf
    cF
    @5
    @72
    poseq.2
    orderseqlem
    ad2antll
    3jca
    @26
    @74
    @75
    @137
    cR
    potr
    sylancr
    impcom
    anim12i
    anassrs
    @152
    sylan2
    exp32
    @131
    @155
    @123
    @125
    @131
    @142
    @121
    @154
    @122
    @142
    @144
    @131
    @121
    @145
    @131
    @143
    @83
    @73
    @81
    vy
    @72
    @82
    raleq
    anbi2d
    syl5bb
    @131
    @153
    @86
    @76
    @131
    @75
    @84
    @137
    @85
    cR
    @72
    @82
    @3
    fveq2
    @72
    @82
    @5
    fveq2
    breq12d
    anbi2d
    anbi12d
    imbi1d
    syl5ibcom
    adantr
    @129
    @132
    @123
    @125
    @129
    @132
    @123
    w3a
    #
    @67
    @119
    @159
    @128
    @60
    vy
    @82
    wral
    #
    @82
    @0
    cfv
    #
    @85
    cR
    wbr
    #
    @67
    @127
    @128
    @132
    @123
    simp1r
    @129
    @132
    @123
    @160
    @129
    @132
    wa
    @82
    @72
    wss
    #
    @123
    @160
    wi
    @127
    @132
    @163
    @128
    @127
    @132
    @163
    @72
    @82
    onelss
    imp
    adantlr
    @163
    @121
    @160
    @122
    @163
    @121
    @71
    vy
    @82
    wral
    #
    @83
    wa
    #
    @160
    @163
    @73
    @164
    @83
    @71
    vy
    @82
    @72
    ssralv
    anim1d
    @165
    @141
    vy
    @82
    wral
    @160
    @71
    @81
    vy
    @82
    r19.26
    @141
    @60
    vy
    @82
    @146
    ralimi
    sylbir
    syl6
    adantrd
    syl
    3impia
    @132
    @123
    @162
    @129
    @123
    @132
    @162
    @73
    @86
    @132
    @162
    wi
    #
    @83
    @76
    @73
    @86
    @166
    @132
    @73
    @86
    @162
    @132
    @73
    @161
    @84
    wceq
    #
    @86
    @162
    wi
    @71
    @167
    vy
    @82
    @72
    vy
    vw
    weq
    @16
    @161
    @70
    @84
    @15
    @82
    @0
    fveq2
    @15
    @82
    @3
    fveq2
    eqeq12d
    rspcv
    @167
    @162
    @86
    @161
    @84
    @85
    cR
    breq1
    biimprd
    syl6
    com3l
    imp
    ad2ant2rl
    impcom
    3adant1
    @66
    @160
    @162
    wa
    vt
    @82
    con0
    vt
    vw
    weq
    #
    @62
    @160
    @65
    @162
    @60
    vy
    @61
    @82
    raleq
    @168
    @63
    @161
    @64
    @85
    cR
    @61
    @82
    @0
    fveq2
    @61
    @82
    @5
    fveq2
    breq12d
    anbi12d
    rspcev
    syl12anc
    a1d
    3exp
    3jaod
    mpd
    rexlimivv
    sylbir
    impcom
    jca31
    an4s
    syl2anb
    @46
    @47
    @48
    vy
    @61
    wral
    #
    @63
    @61
    @34
    cfv
    #
    cR
    wbr
    #
    wa
    #
    vt
    con0
    wrex
    #
    wa
    @68
    vf
    vg
    @0
    @5
    cS
    @53
    @109
    @54
    @36
    @47
    @45
    @173
    @55
    @45
    @39
    vy
    @61
    wral
    #
    @61
    @28
    cfv
    #
    @170
    cR
    wbr
    #
    wa
    #
    vt
    con0
    wrex
    @54
    @173
    @44
    @177
    vx
    vt
    con0
    vx
    vt
    weq
    #
    @40
    @174
    @43
    @176
    @39
    vy
    @18
    @61
    raleq
    @178
    @41
    @175
    @42
    @170
    cR
    @18
    @61
    @28
    fveq2
    @18
    @61
    @34
    fveq2
    breq12d
    anbi12d
    cbvrexv
    @54
    @177
    @172
    vt
    con0
    @54
    @174
    @169
    @176
    @171
    @54
    @39
    @48
    vy
    @61
    @56
    ralbidv
    @54
    @175
    @63
    @170
    cR
    @61
    @28
    @0
    fveq1
    breq1d
    anbi12d
    rexbidv
    syl5bb
    anbi12d
    @116
    @47
    @58
    @173
    @67
    @116
    @35
    @13
    @11
    @117
    anbi2d
    @116
    @172
    @66
    vt
    con0
    @116
    @169
    @62
    @171
    @65
    @116
    @48
    @60
    vy
    @61
    @116
    @38
    @59
    @16
    @118
    eqeq2d
    ralbidv
    @116
    @170
    @64
    @63
    cR
    @61
    @34
    @5
    fveq1
    breq2d
    anbi12d
    rexbidv
    anbi12d
    poseq.3
    brab
    sylibr
    pm3.2i
    a1i
    rgen3
    va
    vb
    vc
    cF
    cS
    df-po
    mpbir
end
