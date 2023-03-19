include "word.mm"
include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wsmo.mm"
include "w3a.mm"
include "wex.mm"
include "csuc.mm"
include "cdm.mm"
include "wfo.mm"
include "cep.mm"
include "wiso.mm"
include "wf1o.mm"
include "cvv.mm"
include "wwe.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssexg.mm"
include "mpan.mm"
include "onss.mm"
include "syl5ss.mm"
include "epweon.mm"
include "wess.mm"
include "mpisyl.mm"
include "oiiso.mm"
include "syl2anc.mm"
include "ad2antlr.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "3syl.mm"
include "fof.mm"
include "fss.mm"
include "sylancl.mm"
include "syl.mm"
include "oion.mm"
include "simplr.mm"
include "wb.mm"
include "eloni.mm"
include "smoiso2.mm"
include "syl2an.mm"
include "biimpar.mm"
include "simprd.mm"
include "syl21anc.mm"
include "smorndom.mm"
include "syl3anc.mm"
include "onsssuc.mm"
include "mpbid.mm"
include "adantrr.mm"
include "ccom.mm"
include "vex.mm"
include "oiexg.mm"
include "coexg.mm"
include "sylancr.mm"
include "simprl.mm"
include "fco.mm"
include "simpr.mm"
include "ordsson.mm"
include "ad2antrr.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "wfn.mm"
include "ffn.mm"
include "jca.mm"
include "smoel2.mm"
include "sylan.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "raleqbi1dv.mm"
include "weq.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"
include "simprbi.mm"
include "rspccv.mm"
include "sylc.mm"
include "adantr.mm"
include "ordtr1.mm"
include "ancomsd.mm"
include "imp.mm"
include "fvco3.mm"
include "3eltr4d.mm"
include "ralrimivva.mm"
include "issmo2.mm"
include "syl13anc.mm"
include "c0.mm"
include "wne.mm"
include "rabn0.mm"
include "cint.mm"
include "sseq2d.mm"
include "inteqi.mm"
include "onint.mm"
include "syl5eqel.mm"
include "sylan2br.mm"
include "elrab.mm"
include "sylib.mm"
include "ex.mm"
include "adantl.mm"
include "simpr2.mm"
include "simp3.mm"
include "eleq2i.mm"
include "wn.mm"
include "simp21.mm"
include "simp1l.mm"
include "fssd.mm"
include "simp22.mm"
include "ffvelrnd.mm"
include "simp1r.mm"
include "ontr1.mm"
include "3impib.mm"
include "ontri1.mm"
include "simp23.mm"
include "simpl1.mm"
include "sstr.mm"
include "anim12i.mm"
include "rabid.mm"
include "sylibr.mm"
include "onnmin.mm"
include "expr.mm"
include "syl31anc.mm"
include "sylbird.mm"
include "con4d.mm"
include "syl5bi.mm"
include "mpd.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "sylanbrc.mm"
include "expcom.mm"
include "3expib.mm"
include "com13.mm"
include "syld.mm"
include "com23.mm"
include "imp31.mm"
include "foelrn.mm"
include "simpllr.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "syl6.mm"
include "sylancom.mm"
include "sylibrd.mm"
include "reximdva.mm"
include "ralimdv.mm"
include "impr.mm"
include "3jca.mm"
include "feq1.mm"
include "smoeq.mm"
include "fveq1.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "spcegv.mm"
include "feq2.mm"
include "rexeq.mm"
include "3anbi13d.mm"
include "exbidv.mm"
include "rspcev.mm"
include "exlimdv.mm"

theorem cofsmo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let cK: class K
  let cO: class O
  let vs: setvar s
  let vt: setvar t
  assume cofsmo.1: |- C = { y e. B | A. w e. y ( f ` w ) e. ( f ` y ) }
  assume cofsmo.2: |- K = |^| { x e. B | z C_ ( f ` x ) }
  assume cofsmo.3: |- O = OrdIso ( _E , C )

  disjoint f g
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint A f
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g z
  disjoint A g
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint f y
  disjoint B f
  disjoint v y
  disjoint B v
  disjoint w y
  disjoint B w
  disjoint x y
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C v
  disjoint K v
  disjoint K w
  disjoint K y
  disjoint O g
  disjoint O v
  disjoint O x
  disjoint O z
  disjoint f s
  disjoint f t
  disjoint g s
  disjoint g t
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s z
  disjoint A s
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint A t
  disjoint s y
  disjoint B s
  disjoint t y
  disjoint B t
  disjoint O s
  disjoint O t
  assert |- ( ( Ord A /\ B e. On ) -> ( E. f ( f : B --> A /\ A. z e. A E. w e. B z C_ ( f ` w ) ) -> E. x e. suc B E. g ( g : x --> A /\ Smo g /\ A. z e. A E. v e. x z C_ ( g ` v ) ) ) )

  proof
    cA
    word
    #
    cB
    con0
    wcel
    #
    wa
    #
    cB
    cA
    vf
    cv
    #
    wf
    #
    vz
    cv
    #
    vw
    cv
    #
    @3
    cfv
    #
    wss
    #
    vw
    cB
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    vx
    cv
    #
    cA
    vg
    cv
    #
    wf
    #
    @13
    wsmo
    #
    @5
    vv
    cv
    #
    @13
    cfv
    #
    wss
    #
    vv
    @12
    wrex
    #
    vz
    cA
    wral
    #
    w3a
    #
    vg
    wex
    #
    vx
    cB
    csuc
    #
    wrex
    #
    vf
    @2
    @11
    @24
    @2
    @11
    wa
    #
    cO
    cdm
    #
    @23
    wcel
    #
    @26
    cA
    @13
    wf
    #
    @15
    @18
    vv
    @26
    wrex
    #
    vz
    cA
    wral
    #
    w3a
    #
    vg
    wex
    #
    @24
    @2
    @4
    @27
    @10
    @2
    @4
    wa
    #
    @26
    cB
    wss
    #
    @27
    @33
    @26
    cB
    cO
    wf
    #
    cO
    wsmo
    #
    cB
    word
    #
    @34
    @33
    @26
    cC
    cO
    wfo
    #
    @35
    @33
    @26
    cC
    cep
    cep
    cO
    wiso
    #
    @26
    cC
    cO
    wf1o
    @38
    @1
    @39
    @0
    @4
    @1
    cC
    cvv
    wcel
    #
    cC
    cep
    wwe
    #
    @39
    cC
    cB
    wss
    #
    @1
    @40
    cC
    @7
    vy
    cv
    #
    @3
    cfv
    #
    wcel
    #
    vw
    @43
    wral
    #
    vy
    cB
    crab
    #
    cB
    cofsmo.1
    @46
    vy
    cB
    ssrab2
    eqsstri
    #
    cC
    cB
    con0
    ssexg
    mpan
    #
    @1
    cC
    con0
    wss
    #
    con0
    cep
    wwe
    @41
    @1
    cC
    cB
    con0
    @48
    cB
    onss
    #
    syl5ss
    #
    epweon
    cC
    con0
    cep
    wess
    mpisyl
    cC
    cep
    cO
    cvv
    cofsmo.3
    oiiso
    syl2anc
    ad2antlr
    #
    @26
    cC
    cep
    cep
    cO
    isof1o
    @26
    cC
    cO
    f1ofo
    3syl
    #
    @38
    @26
    cC
    cO
    wf
    #
    @42
    @35
    @26
    cC
    cO
    fof
    #
    @48
    @26
    cC
    cB
    cO
    fss
    sylancl
    syl
    #
    @33
    @26
    con0
    wcel
    #
    @1
    @39
    @36
    @1
    @58
    @0
    @4
    @1
    @40
    @58
    @49
    cC
    cep
    cO
    cvv
    cofsmo.3
    oion
    syl
    ad2antlr
    #
    @0
    @1
    @4
    simplr
    #
    @53
    @58
    @1
    wa
    #
    @39
    wa
    @38
    @36
    @61
    @38
    @36
    wa
    #
    @39
    @58
    @26
    word
    #
    @50
    @62
    @39
    wb
    @1
    @26
    eloni
    #
    @52
    @26
    cC
    cO
    smoiso2
    syl2an
    biimpar
    simprd
    syl21anc
    #
    @1
    @37
    @0
    @4
    cB
    eloni
    ad2antlr
    @26
    cB
    cO
    smorndom
    syl3anc
    @33
    @58
    @1
    @34
    @27
    wb
    @59
    @60
    @26
    cB
    onsssuc
    syl2anc
    mpbid
    adantrr
    @25
    @3
    cO
    ccom
    #
    cvv
    wcel
    #
    @26
    cA
    @66
    wf
    #
    @66
    wsmo
    #
    @5
    @16
    @66
    cfv
    #
    wss
    #
    vv
    @26
    wrex
    #
    vz
    cA
    wral
    #
    w3a
    #
    @32
    @25
    @3
    cvv
    wcel
    cO
    cvv
    wcel
    #
    @67
    vf
    vex
    @1
    @75
    @0
    @11
    @1
    @40
    @75
    @49
    cC
    cep
    cO
    cvv
    cofsmo.3
    oiexg
    syl
    ad2antlr
    @3
    cO
    cvv
    cvv
    coexg
    sylancr
    @25
    @68
    @69
    @73
    @25
    @4
    @35
    @68
    @2
    @4
    @10
    simprl
    @2
    @4
    @35
    @10
    @57
    adantrr
    @26
    cB
    cA
    @3
    cO
    fco
    #
    syl2anc
    @2
    @4
    @69
    @10
    @33
    @68
    cA
    con0
    wss
    #
    @63
    vt
    cv
    #
    @66
    cfv
    #
    vs
    cv
    #
    @66
    cfv
    #
    wcel
    #
    vt
    @80
    wral
    vs
    @26
    wral
    #
    @69
    @33
    @4
    @35
    @68
    @2
    @4
    simpr
    @57
    @76
    syl2anc
    @0
    @77
    @1
    @4
    cA
    ordsson
    #
    ad2antrr
    @33
    @58
    @63
    @59
    @64
    syl
    @33
    @82
    vs
    vt
    @26
    @80
    @33
    @80
    @26
    wcel
    #
    @78
    @80
    wcel
    #
    wa
    #
    wa
    #
    @78
    cO
    cfv
    #
    @3
    cfv
    #
    @80
    cO
    cfv
    #
    @3
    cfv
    #
    @79
    @81
    @88
    @91
    cC
    wcel
    #
    @89
    @91
    wcel
    #
    @90
    @92
    wcel
    #
    @33
    @55
    @85
    @93
    @87
    @33
    @38
    @55
    @54
    @56
    syl
    @85
    @86
    simpl
    @26
    cC
    @80
    cO
    ffvelrn
    syl2an
    @33
    cO
    @26
    wfn
    #
    @36
    wa
    @87
    @94
    @33
    @96
    @36
    @33
    @38
    @55
    @96
    @54
    @56
    @26
    cC
    cO
    ffn
    3syl
    @65
    jca
    @26
    @80
    @78
    cO
    smoel2
    sylan
    @93
    @12
    @3
    cfv
    #
    @92
    wcel
    #
    vx
    @91
    wral
    #
    @94
    @95
    wi
    @93
    @91
    cB
    wcel
    @99
    @97
    @5
    @3
    cfv
    #
    wcel
    #
    vx
    @5
    wral
    #
    @99
    vz
    @91
    cB
    cC
    @101
    @98
    vx
    @5
    @91
    @5
    @91
    wceq
    @100
    @92
    @97
    @5
    @91
    @3
    fveq2
    eleq2d
    raleqbi1dv
    cC
    @47
    @102
    vz
    cB
    crab
    cofsmo.1
    @46
    @102
    vy
    vz
    cB
    @46
    @97
    @44
    wcel
    #
    vx
    @43
    wral
    vy
    vz
    weq
    #
    @102
    @45
    @103
    vw
    vx
    @43
    vw
    vx
    weq
    #
    @7
    @97
    @44
    @6
    @12
    @3
    fveq2
    #
    eleq1d
    cbvralv
    @103
    @101
    vx
    @43
    @5
    @104
    @44
    @100
    @97
    @43
    @5
    @3
    fveq2
    eleq2d
    raleqbi1dv
    syl5bb
    cbvrabv
    eqtri
    elrab2
    simprbi
    @98
    @95
    vx
    @89
    @91
    @12
    @89
    wceq
    @97
    @90
    @92
    @12
    @89
    @3
    fveq2
    eleq1d
    rspccv
    syl
    sylc
    @88
    @35
    @78
    @26
    wcel
    #
    @79
    @90
    wceq
    @33
    @35
    @87
    @57
    adantr
    #
    @33
    @87
    @107
    @33
    @58
    @63
    @87
    @107
    wi
    @59
    @64
    @63
    @86
    @85
    @107
    @78
    @80
    @26
    ordtr1
    ancomsd
    3syl
    imp
    @26
    cB
    @78
    @3
    cO
    fvco3
    syl2anc
    @88
    @35
    @85
    @81
    @92
    wceq
    @108
    @33
    @85
    @86
    simprl
    @26
    cB
    @80
    @3
    cO
    fvco3
    syl2anc
    3eltr4d
    ralrimivva
    @68
    @77
    @63
    @83
    w3a
    @69
    vs
    vt
    @26
    cA
    @66
    issmo2
    imp
    syl13anc
    adantrr
    @2
    @4
    @10
    @73
    @33
    @9
    @72
    vz
    cA
    @33
    @9
    @72
    @33
    @9
    wa
    #
    cK
    @16
    cO
    cfv
    #
    wceq
    #
    vv
    @26
    wrex
    #
    @72
    @109
    @38
    cK
    cC
    wcel
    #
    @112
    @33
    @38
    @9
    @54
    adantr
    @2
    @4
    @9
    @113
    @2
    @9
    @4
    @113
    @2
    @9
    cK
    cB
    wcel
    #
    @5
    cK
    @3
    cfv
    #
    wss
    #
    wa
    #
    @4
    @113
    wi
    @1
    @9
    @117
    wi
    @0
    @1
    @9
    @117
    @1
    @9
    wa
    #
    cK
    @8
    vw
    cB
    crab
    #
    wcel
    #
    @117
    @9
    @1
    @119
    c0
    wne
    #
    @120
    @8
    vw
    cB
    rabn0
    @1
    @119
    con0
    wss
    #
    @121
    @120
    @1
    @119
    cB
    con0
    @8
    vw
    cB
    ssrab2
    @51
    syl5ss
    #
    @122
    @121
    wa
    cK
    @119
    cint
    #
    @119
    cK
    @5
    @97
    wss
    #
    vx
    cB
    crab
    #
    cint
    @124
    cofsmo.2
    @126
    @119
    @125
    @8
    vx
    vw
    cB
    vx
    vw
    weq
    @97
    @7
    @5
    @12
    @6
    @3
    fveq2
    sseq2d
    cbvrabv
    inteqi
    eqtri
    #
    @119
    onint
    syl5eqel
    sylan
    sylan2br
    #
    @8
    @116
    vw
    cK
    cB
    @6
    cK
    wceq
    @7
    @115
    @5
    @6
    cK
    @3
    fveq2
    sseq2d
    elrab
    sylib
    ex
    adantl
    @4
    @117
    @2
    @113
    @4
    @114
    @116
    @2
    @113
    wi
    @2
    @4
    @114
    @116
    w3a
    #
    @113
    @2
    @129
    wa
    #
    @114
    @7
    @115
    wcel
    #
    vw
    cK
    wral
    #
    @113
    @2
    @4
    @114
    @116
    simpr2
    @130
    @131
    vw
    cK
    @2
    @129
    @6
    cK
    wcel
    #
    @131
    @2
    @129
    @133
    w3a
    #
    @133
    @131
    @2
    @129
    @133
    simp3
    #
    @133
    @6
    @124
    wcel
    #
    @134
    @131
    cK
    @124
    @6
    @127
    eleq2i
    @134
    @131
    @136
    @134
    @131
    wn
    #
    @115
    @7
    wss
    #
    @136
    wn
    #
    @134
    @115
    con0
    wcel
    @7
    con0
    wcel
    @138
    @137
    wb
    @134
    cB
    con0
    cK
    @3
    @134
    cB
    cA
    con0
    @3
    @2
    @4
    @114
    @116
    @133
    simp21
    @134
    @0
    @77
    @0
    @1
    @129
    @133
    simp1l
    @84
    syl
    fssd
    #
    @2
    @4
    @114
    @116
    @133
    simp22
    #
    ffvelrnd
    @134
    cB
    con0
    @6
    @3
    @140
    @134
    @1
    @133
    @114
    @6
    cB
    wcel
    #
    @0
    @1
    @129
    @133
    simp1r
    #
    @135
    @141
    @1
    @133
    @114
    @142
    @6
    cK
    cB
    ontr1
    3impib
    #
    syl3anc
    ffvelrnd
    @115
    @7
    ontri1
    syl2anc
    @134
    @1
    @133
    @114
    @116
    @138
    @139
    wi
    @143
    @135
    @141
    @2
    @4
    @114
    @116
    @133
    simp23
    @1
    @133
    @114
    w3a
    #
    @116
    @138
    @139
    @145
    @116
    @138
    wa
    #
    wa
    #
    @122
    @6
    @119
    wcel
    #
    @139
    @147
    @1
    @122
    @1
    @133
    @114
    @146
    simpl1
    @123
    syl
    @147
    @142
    @8
    wa
    @148
    @145
    @142
    @146
    @8
    @144
    @5
    @115
    @7
    sstr
    anim12i
    @8
    vw
    cB
    rabid
    sylibr
    @119
    @6
    onnmin
    syl2anc
    expr
    syl31anc
    sylbird
    con4d
    syl5bi
    mpd
    3expia
    ralrimiv
    @46
    @132
    vy
    cK
    cB
    cC
    @45
    @131
    vw
    @43
    cK
    @43
    cK
    wceq
    @44
    @115
    @7
    @43
    cK
    @3
    fveq2
    eleq2d
    raleqbi1dv
    cofsmo.1
    elrab2
    sylanbrc
    expcom
    3expib
    com13
    syld
    com23
    imp31
    vv
    @26
    cC
    cK
    cO
    foelrn
    syl2anc
    @109
    @111
    @71
    vv
    @26
    @109
    @16
    @26
    wcel
    #
    wa
    #
    @111
    @5
    @110
    @3
    cfv
    #
    wss
    #
    @71
    @109
    @111
    @152
    wi
    #
    @149
    @33
    @9
    @1
    @153
    @0
    @1
    @4
    @9
    simpllr
    @118
    @120
    @153
    @128
    @120
    @111
    @110
    @119
    wcel
    #
    @152
    @111
    @120
    @154
    cK
    @110
    @119
    eleq1
    biimpcd
    @154
    @110
    cB
    wcel
    @152
    @125
    @152
    vx
    @110
    cB
    @119
    @12
    @110
    wceq
    @97
    @151
    @5
    @12
    @110
    @3
    fveq2
    sseq2d
    @8
    @125
    vw
    vx
    cB
    @105
    @7
    @97
    @5
    @106
    sseq2d
    cbvrabv
    elrab2
    simprbi
    syl6
    syl
    sylancom
    adantr
    @150
    @70
    @151
    @5
    @109
    @149
    @35
    @70
    @151
    wceq
    @33
    @35
    @9
    @149
    @57
    ad2antrr
    @26
    cB
    @16
    @3
    cO
    fvco3
    sylancom
    sseq2d
    sylibrd
    reximdva
    mpd
    ex
    ralimdv
    impr
    3jca
    @31
    @74
    vg
    @66
    cvv
    @13
    @66
    wceq
    #
    @28
    @68
    @15
    @69
    @30
    @73
    @26
    cA
    @13
    @66
    feq1
    @13
    @66
    smoeq
    @155
    @29
    @72
    vz
    cA
    @155
    @18
    @71
    vv
    @26
    @155
    @17
    @70
    @5
    @16
    @13
    @66
    fveq1
    sseq2d
    rexbidv
    ralbidv
    3anbi123d
    spcegv
    sylc
    @22
    @32
    vx
    @26
    @23
    @12
    @26
    wceq
    #
    @21
    @31
    vg
    @156
    @14
    @28
    @20
    @30
    @15
    @12
    @26
    cA
    @13
    feq2
    @156
    @19
    @29
    vz
    cA
    @18
    vv
    @12
    @26
    rexeq
    ralbidv
    3anbi13d
    exbidv
    rspcev
    syl2anc
    ex
    exlimdv
end
