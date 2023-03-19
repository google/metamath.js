include "ctb.mm"
include "wcel.mm"
include "c2ndc.mm"
include "wa.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "w3a.mm"
include "wrex.mm"
include "simpr.mm"
include "is2ndc.mm"
include "sylib.mm"
include "cid.mm"
include "wf.mm"
include "c1st.mm"
include "c2nd.mm"
include "wral.mm"
include "wex.mm"
include "cxp.mm"
include "cvv.mm"
include "vex.mm"
include "xpex.mm"
include "wel.mm"
include "copab.mm"
include "3simpa.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "3sstr4i.mm"
include "ssdomg.mm"
include "mp2.mm"
include "cen.mm"
include "xpdom1.mm"
include "omex.mm"
include "xpdom2.mm"
include "domtr.mm"
include "syl2anc.mm"
include "xpomen.mm"
include "domentr.mm"
include "sylancl.mm"
include "adantr.mm"
include "ad2antll.mm"
include "sylancr.mm"
include "cop.mm"
include "wrel.mm"
include "relopabi.mm"
include "1st2nd.mm"
include "eqeltrrd.mm"
include "df-br.mm"
include "fvex.mm"
include "simpl.mm"
include "eleq1d.mm"
include "sseq1.mm"
include "sseq2.mm"
include "bi2anan9.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "braba.mm"
include "bitr3i.mm"
include "simp3bi.mm"
include "syl.mm"
include "fvi.mm"
include "ad3antrrr.mm"
include "rexeqdv.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "anbi12d.mm"
include "axcc4dom.mm"
include "ad2antrr.mm"
include "feq3d.mm"
include "anbi1d.mm"
include "crn.mm"
include "ctop.mm"
include "2ndctop.mm"
include "adantl.mm"
include "frn.mm"
include "ad2antrl.mm"
include "bastg.mm"
include "syl6sseqr.mm"
include "sstrd.mm"
include "simprrl.mm"
include "simprr.mm"
include "ad2antlr.mm"
include "eleqtrrd.mm"
include "simprrr.mm"
include "tg2.mm"
include "eqeq2i.mm"
include "biimpi.mm"
include "sseqtrd.mm"
include "simprl.mm"
include "sseldd.mm"
include "syl6req.mm"
include "wfn.mm"
include "ffn.mm"
include "simplrl.mm"
include "weq.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "syl3anbrc.mm"
include "fnfvelrn.mm"
include "wi.mm"
include "simplll.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "op1st.mm"
include "sseq1i.mm"
include "op2nd.mm"
include "sseq2i.mm"
include "anbi12i.mm"
include "simplrr.mm"
include "jca.mm"
include "ex.mm"
include "syl5bi.mm"
include "syldc.mm"
include "exp4c.mm"
include "imp41.mm"
include "eleq2.mm"
include "rexlimddv.mm"
include "expr.mm"
include "ralrimivv.mm"
include "basgen2.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "tgclb.mm"
include "sylibr.mm"
include "ccrd.mm"
include "cdm.mm"
include "wfo.mm"
include "con0.mm"
include "omelon.mm"
include "ondomen.mm"
include "dffn4.mm"
include "fodomnum.mm"
include "sylc.mm"
include "eqcomd.mm"
include "breq1.mm"
include "eqeq2d.mm"
include "syl13anc.mm"
include "sylbid.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem 2ndcctbss
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cS: class S
  let cJ: class J
  let cX: class X
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vt: setvar t
  let vx: setvar x
  assume 2ndcctbss.1: |- X = U. B
  assume 2ndcctbss.2: |- J = ( topGen ` B )
  assume 2ndcctbss.3: |- S = { <. u , v >. | ( u e. c /\ v e. c /\ E. w e. B ( u C_ w /\ w C_ v ) ) }

  disjoint b c
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint B b
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint B c
  disjoint u v
  disjoint u w
  disjoint B u
  disjoint v w
  disjoint B v
  disjoint B w
  disjoint J b
  disjoint J c
  disjoint b d
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b o
  disjoint b t
  disjoint b x
  disjoint c d
  disjoint c f
  disjoint c m
  disjoint c n
  disjoint c o
  disjoint c t
  disjoint c x
  disjoint d f
  disjoint d m
  disjoint d n
  disjoint d o
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint B d
  disjoint f m
  disjoint f n
  disjoint f o
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint B f
  disjoint m n
  disjoint m o
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint B m
  disjoint n o
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint B n
  disjoint o t
  disjoint o u
  disjoint o v
  disjoint o w
  disjoint o x
  disjoint B o
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint B t
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint B x
  disjoint J d
  disjoint J f
  disjoint J m
  disjoint J n
  disjoint J o
  disjoint J t
  disjoint J x
  disjoint S d
  disjoint S f
  disjoint S m
  disjoint S n
  disjoint S o
  disjoint S t
  disjoint S x
  assert |- ( ( B e. TopBases /\ J e. 2ndc ) -> E. b e. TopBases ( b ~<_ _om /\ b C_ B /\ J = ( topGen ` b ) ) )

  proof
    cB
    ctb
    wcel
    #
    cJ
    c2ndc
    wcel
    #
    wa
    #
    vc
    cv
    #
    com
    cdom
    wbr
    #
    @3
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    vb
    cv
    #
    com
    cdom
    wbr
    #
    @8
    cB
    wss
    #
    cJ
    @8
    ctg
    cfv
    #
    wceq
    #
    w3a
    #
    vb
    ctb
    wrex
    #
    vc
    ctb
    @2
    @1
    @7
    vc
    ctb
    wrex
    @0
    @1
    simpr
    vc
    cJ
    is2ndc
    sylib
    @2
    @3
    ctb
    wcel
    #
    @7
    wa
    #
    wa
    #
    cS
    cB
    cid
    cfv
    #
    vf
    cv
    #
    wf
    #
    vx
    cv
    #
    c1st
    cfv
    #
    @21
    @19
    cfv
    #
    wss
    #
    @23
    @21
    c2nd
    cfv
    #
    wss
    #
    wa
    #
    vx
    cS
    wral
    #
    wa
    #
    vf
    wex
    #
    @14
    @17
    cS
    com
    cdom
    wbr
    #
    @22
    vw
    cv
    #
    wss
    #
    @32
    @25
    wss
    #
    wa
    #
    vw
    @18
    wrex
    #
    vx
    cS
    wral
    @30
    @17
    cS
    @3
    @3
    cxp
    #
    cdom
    wbr
    #
    @37
    com
    cdom
    wbr
    #
    @31
    @37
    cvv
    wcel
    cS
    @37
    wss
    @38
    @3
    @3
    vc
    vex
    #
    @40
    xpex
    vu
    vc
    wel
    #
    vv
    vc
    wel
    #
    vu
    cv
    #
    @32
    wss
    #
    @32
    vv
    cv
    #
    wss
    #
    wa
    #
    vw
    cB
    wrex
    #
    w3a
    #
    vu
    vv
    copab
    @41
    @42
    wa
    #
    vu
    vv
    copab
    cS
    @37
    @49
    @50
    vu
    vv
    @41
    @42
    @48
    3simpa
    ssopab2i
    2ndcctbss.3
    vu
    vv
    @3
    @3
    df-xp
    3sstr4i
    cS
    @37
    cvv
    ssdomg
    mp2
    @7
    @39
    @2
    @15
    @4
    @39
    @6
    @4
    @37
    com
    com
    cxp
    #
    cdom
    wbr
    #
    @51
    com
    cen
    wbr
    @39
    @4
    @37
    com
    @3
    cxp
    #
    cdom
    wbr
    @53
    @51
    cdom
    wbr
    @52
    @3
    com
    @3
    @40
    xpdom1
    @3
    com
    com
    omex
    xpdom2
    @37
    @53
    @51
    domtr
    syl2anc
    xpomen
    @37
    @51
    com
    domentr
    sylancl
    adantr
    ad2antll
    cS
    @37
    com
    domtr
    sylancr
    #
    @17
    @36
    vx
    cS
    @17
    @21
    cS
    wcel
    #
    wa
    #
    @36
    @35
    vw
    cB
    wrex
    #
    @56
    @22
    @25
    cop
    #
    cS
    wcel
    #
    @57
    @56
    @21
    @58
    cS
    @56
    cS
    wrel
    @55
    @21
    @58
    wceq
    @49
    vu
    vv
    cS
    2ndcctbss.3
    relopabi
    @17
    @55
    simpr
    #
    @21
    cS
    1st2nd
    sylancr
    @60
    eqeltrrd
    @59
    @22
    @3
    wcel
    #
    @25
    @3
    wcel
    #
    @57
    @59
    @22
    @25
    cS
    wbr
    @61
    @62
    @57
    w3a
    #
    @22
    @25
    cS
    df-br
    @49
    @63
    vu
    vv
    @22
    @25
    cS
    @21
    c1st
    fvex
    @21
    c2nd
    fvex
    @43
    @22
    wceq
    #
    @45
    @25
    wceq
    #
    wa
    #
    @41
    @61
    @42
    @62
    @48
    @57
    @66
    @43
    @22
    @3
    @64
    @65
    simpl
    eleq1d
    @66
    @45
    @25
    @3
    @64
    @65
    simpr
    eleq1d
    @66
    @47
    @35
    vw
    cB
    @64
    @44
    @33
    @65
    @46
    @34
    @43
    @22
    @32
    sseq1
    @45
    @25
    @32
    sseq2
    bi2anan9
    rexbidv
    3anbi123d
    2ndcctbss.3
    braba
    bitr3i
    simp3bi
    syl
    @56
    @35
    vw
    @18
    cB
    @0
    @18
    cB
    wceq
    #
    @1
    @16
    @55
    cB
    ctb
    fvi
    #
    ad3antrrr
    rexeqdv
    mpbird
    ralrimiva
    @35
    @27
    vw
    @18
    vf
    vx
    cS
    cB
    cid
    fvex
    @32
    @23
    wceq
    @33
    @24
    @34
    @26
    @32
    @23
    @22
    sseq2
    @32
    @23
    @25
    sseq1
    anbi12d
    axcc4dom
    syl2anc
    @17
    @29
    @14
    vf
    @17
    @29
    cS
    cB
    @19
    wf
    #
    @28
    wa
    #
    @14
    @17
    @20
    @69
    @28
    @17
    @18
    cB
    @19
    cS
    @0
    @67
    @1
    @16
    @68
    ad2antrr
    feq3d
    anbi1d
    @17
    @70
    @14
    @17
    @70
    wa
    #
    @19
    crn
    #
    ctb
    wcel
    #
    @72
    com
    cdom
    wbr
    #
    @72
    cB
    wss
    #
    cJ
    @72
    ctg
    cfv
    #
    wceq
    #
    @14
    @71
    @76
    ctop
    wcel
    @73
    @71
    @76
    cJ
    ctop
    @71
    cJ
    ctop
    wcel
    #
    @72
    cJ
    wss
    vt
    vb
    wel
    #
    @8
    vo
    cv
    #
    wss
    #
    wa
    #
    vb
    @72
    wrex
    #
    vt
    @80
    wral
    vo
    cJ
    wral
    @76
    cJ
    wceq
    @2
    @78
    @16
    @70
    @1
    @78
    @0
    cJ
    2ndctop
    adantl
    ad2antrr
    #
    @71
    @72
    cB
    cJ
    @69
    @75
    @17
    @28
    cS
    cB
    @19
    frn
    ad2antrl
    #
    @71
    cB
    cB
    ctg
    cfv
    #
    cJ
    @0
    cB
    @86
    wss
    #
    @1
    @16
    @70
    cB
    ctb
    bastg
    #
    ad3antrrr
    2ndcctbss.2
    syl6sseqr
    sstrd
    @71
    @83
    vo
    vt
    cJ
    @80
    @17
    @70
    @80
    cJ
    wcel
    #
    vt
    vo
    wel
    #
    wa
    #
    @83
    @17
    @70
    @91
    wa
    #
    wa
    #
    vt
    vd
    wel
    #
    vd
    cv
    #
    @80
    wss
    #
    wa
    #
    @83
    vd
    @3
    @93
    @80
    @5
    wcel
    @90
    @97
    vd
    @3
    wrex
    @93
    @80
    cJ
    @5
    @17
    @70
    @89
    @90
    simprrl
    @16
    @6
    @2
    @92
    @15
    @4
    @6
    simprr
    ad2antlr
    #
    eleqtrrd
    @17
    @70
    @89
    @90
    simprrr
    vd
    @80
    @3
    vt
    cv
    #
    tg2
    syl2anc
    @93
    vd
    vc
    wel
    #
    @97
    wa
    #
    wa
    #
    vt
    vm
    wel
    #
    vm
    cv
    #
    @95
    wss
    #
    wa
    #
    @83
    vm
    cB
    @102
    @95
    @86
    wcel
    @94
    @106
    vm
    cB
    wrex
    @102
    @3
    @86
    @95
    @102
    @3
    @5
    @86
    @17
    @3
    @5
    wss
    #
    @92
    @101
    @15
    @107
    @2
    @7
    @3
    ctb
    bastg
    ad2antrl
    ad2antrr
    @17
    @5
    @86
    wceq
    #
    @92
    @101
    @7
    @108
    @2
    @15
    @6
    @108
    @4
    @6
    @108
    cJ
    @86
    @5
    2ndcctbss.2
    eqeq2i
    biimpi
    adantl
    ad2antll
    ad2antrr
    sseqtrd
    @93
    @100
    @97
    simprl
    #
    sseldd
    @93
    @100
    @94
    @96
    simprrl
    vm
    @95
    cB
    @99
    tg2
    syl2anc
    @102
    @104
    cB
    wcel
    #
    @106
    wa
    #
    wa
    #
    vt
    vn
    wel
    #
    vn
    cv
    #
    @104
    wss
    #
    wa
    #
    @83
    vn
    @3
    @112
    @104
    @5
    wcel
    @103
    @116
    vn
    @3
    wrex
    @112
    cB
    @5
    @104
    @112
    cB
    @86
    @5
    @93
    @87
    @101
    @111
    @0
    @87
    @1
    @16
    @92
    @88
    ad3antrrr
    ad2antrr
    @112
    @5
    cJ
    @86
    @93
    @6
    @101
    @111
    @98
    ad2antrr
    2ndcctbss.2
    syl6req
    sseqtrd
    @102
    @110
    @106
    simprl
    sseldd
    @102
    @110
    @103
    @105
    simprrl
    vn
    @104
    @3
    @99
    tg2
    syl2anc
    @112
    vn
    vc
    wel
    #
    @116
    wa
    #
    wa
    #
    @114
    @95
    cop
    #
    @19
    cfv
    #
    @72
    wcel
    #
    @99
    @121
    wcel
    #
    @121
    @80
    wss
    #
    wa
    #
    @83
    @119
    @19
    cS
    wfn
    #
    @120
    cS
    wcel
    #
    @122
    @102
    @126
    @111
    @118
    @92
    @126
    @17
    @101
    @69
    @126
    @28
    @91
    cS
    cB
    @19
    ffn
    #
    ad2antrr
    ad2antlr
    ad2antrr
    @119
    @117
    @100
    @114
    @32
    wss
    #
    @32
    @95
    wss
    #
    wa
    #
    vw
    cB
    wrex
    #
    @127
    @112
    @117
    @116
    simprl
    @102
    @100
    @111
    @118
    @109
    ad2antrr
    @119
    @110
    @115
    @105
    @132
    @102
    @110
    @106
    @118
    simplrl
    @112
    @117
    @113
    @115
    simprrr
    @111
    @105
    @102
    @118
    @110
    @103
    @105
    simprr
    #
    ad2antlr
    @131
    @115
    @105
    wa
    vw
    @104
    cB
    vw
    vm
    weq
    @129
    @115
    @130
    @105
    @32
    @104
    @114
    sseq2
    @32
    @104
    @95
    sseq1
    anbi12d
    rspcev
    #
    syl12anc
    @127
    @114
    @95
    cS
    wbr
    @117
    @100
    @132
    w3a
    #
    @114
    @95
    cS
    df-br
    @49
    @135
    vu
    vv
    @114
    @95
    cS
    vn
    vex
    #
    vd
    vex
    #
    vu
    vn
    weq
    #
    vv
    vd
    weq
    #
    wa
    #
    @41
    @117
    @42
    @100
    @48
    @132
    @140
    @43
    @114
    @3
    @138
    @139
    simpl
    eleq1d
    @140
    @45
    @95
    @3
    @138
    @139
    simpr
    eleq1d
    @140
    @47
    @131
    vw
    cB
    @138
    @44
    @129
    @139
    @46
    @130
    @43
    @114
    @32
    sseq1
    @45
    @95
    @32
    sseq2
    bi2anan9
    rexbidv
    3anbi123d
    2ndcctbss.3
    braba
    bitr3i
    #
    syl3anbrc
    cS
    @120
    @19
    fnfvelrn
    syl2anc
    @93
    @101
    @111
    @118
    @125
    @92
    @101
    @111
    @118
    @125
    wi
    wi
    wi
    #
    @17
    @28
    @142
    @69
    @91
    @28
    @101
    @111
    @118
    @125
    @101
    @111
    wa
    #
    @118
    wa
    #
    @28
    @120
    c1st
    cfv
    #
    @121
    wss
    #
    @121
    @120
    c2nd
    cfv
    #
    wss
    #
    wa
    #
    @125
    @144
    @127
    @28
    @149
    wi
    @144
    @117
    @100
    @132
    @127
    @143
    @117
    @116
    simprl
    @100
    @97
    @111
    @118
    simplll
    @144
    @110
    @115
    @105
    @132
    @101
    @110
    @106
    @118
    simplrl
    @143
    @117
    @113
    @115
    simprrr
    @111
    @105
    @101
    @118
    @133
    ad2antlr
    @134
    syl12anc
    @141
    syl3anbrc
    @27
    @149
    vx
    @120
    cS
    @21
    @120
    wceq
    #
    @24
    @146
    @26
    @148
    @150
    @22
    @145
    @23
    @121
    @21
    @120
    c1st
    fveq2
    @21
    @120
    @19
    fveq2
    #
    sseq12d
    @150
    @23
    @121
    @25
    @147
    @151
    @21
    @120
    c2nd
    fveq2
    sseq12d
    anbi12d
    rspcv
    syl
    @149
    @114
    @121
    wss
    #
    @121
    @95
    wss
    #
    wa
    #
    @144
    @125
    @146
    @152
    @148
    @153
    @145
    @114
    @121
    @114
    @95
    @136
    @137
    op1st
    sseq1i
    @147
    @95
    @121
    @114
    @95
    @136
    @137
    op2nd
    sseq2i
    anbi12i
    @144
    @154
    @125
    @144
    @154
    wa
    #
    @123
    @124
    @155
    @114
    @121
    @99
    @144
    @152
    @153
    simprl
    @118
    @113
    @143
    @154
    @117
    @113
    @115
    simprl
    ad2antlr
    sseldd
    @155
    @121
    @95
    @80
    @144
    @152
    @153
    simprr
    @143
    @96
    @118
    @154
    @100
    @94
    @96
    @111
    simplrr
    ad2antrr
    sstrd
    jca
    ex
    syl5bi
    syldc
    exp4c
    ad2antlr
    adantl
    imp41
    @82
    @125
    vb
    @121
    @72
    @8
    @121
    wceq
    @79
    @123
    @81
    @124
    @8
    @121
    @99
    eleq2
    @8
    @121
    @80
    sseq1
    anbi12d
    rspcev
    syl2anc
    rexlimddv
    rexlimddv
    rexlimddv
    expr
    ralrimivv
    vo
    vt
    vb
    @72
    cJ
    basgen2
    syl3anc
    #
    @84
    eqeltrd
    @72
    tgclb
    sylibr
    @71
    @72
    cS
    cdom
    wbr
    #
    @31
    @74
    @71
    cS
    ccrd
    cdm
    wcel
    #
    cS
    @72
    @19
    wfo
    #
    @157
    @71
    com
    con0
    wcel
    @31
    @158
    omelon
    @17
    @31
    @70
    @54
    adantr
    #
    com
    cS
    ondomen
    sylancr
    @71
    @126
    @159
    @69
    @126
    @17
    @28
    @128
    ad2antrl
    cS
    @19
    dffn4
    sylib
    cS
    @72
    @19
    fodomnum
    sylc
    @160
    @72
    cS
    com
    domtr
    syl2anc
    @85
    @71
    @76
    cJ
    @156
    eqcomd
    @13
    @74
    @75
    @77
    w3a
    vb
    @72
    ctb
    @8
    @72
    wceq
    #
    @9
    @74
    @10
    @75
    @12
    @77
    @8
    @72
    com
    cdom
    breq1
    @8
    @72
    cB
    sseq1
    @161
    @11
    @76
    cJ
    @8
    @72
    ctg
    fveq2
    eqeq2d
    3anbi123d
    rspcev
    syl13anc
    ex
    sylbid
    exlimdv
    mpd
    rexlimddv
end
