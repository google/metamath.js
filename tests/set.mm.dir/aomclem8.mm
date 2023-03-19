include "wel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cdm.mm"
include "cuni.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "wi.mm"
include "cr1.mm"
include "wral.mm"
include "wrex.mm"
include "copab.mm"
include "cvv.mm"
include "csup.mm"
include "cmpt.mm"
include "crn.mm"
include "cdif.mm"
include "crecs.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cint.mm"
include "wcel.mm"
include "crnk.mm"
include "cep.mm"
include "wceq.mm"
include "csuc.mm"
include "wo.mm"
include "cif.mm"
include "cxp.mm"
include "cin.mm"
include "weq.mm"
include "elequ2.mm"
include "notbid.mm"
include "bi2anan9r.mm"
include "bi2bian9.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "elequ1.mm"
include "breq2.mm"
include "imbi1d.mm"
include "breq1.mm"
include "bibi12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "cbvrexv.mm"
include "cbvopabv.mm"
include "nfcv.mm"
include "nfopab1.mm"
include "nfsup.mm"
include "fveq2.mm"
include "supeq1d.mm"
include "cbvmpt.mm"
include "nffvmpt1.mm"
include "rneq.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "recseq.mm"
include "ax-mp.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfrecs.mm"
include "nfcnv.mm"
include "nfima.mm"
include "nfint.mm"
include "nfel.mm"
include "nfopab2.mm"
include "nfmpt.mm"
include "nffv.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "inteqd.mm"
include "eleq12.mm"
include "syl2an.mm"
include "cbvopab.mm"
include "breqan12d.mm"
include "eqeqan12d.mm"
include "simpl.mm"
include "suceq.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "breq123d.mm"
include "orbi12d.mm"
include "eqid.mm"
include "dmeq.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "fveq1.mm"
include "breqd.mm"
include "anbi2d.mm"
include "orbi2d.mm"
include "opabbidv.mm"
include "eqidd.mm"
include "id.mm"
include "fveq12d.mm"
include "raleqbidv.mm"
include "rexeqbidv.mm"
include "supeq123d.mm"
include "mpteq2dv.mm"
include "difeq1d.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "eleq12d.mm"
include "ifbieq12d.mm"
include "sqxpeqd.mm"
include "ineq12d.mm"
include "cbvmptv.mm"
include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "cfn.mm"
include "neeq1.mm"
include "pweq.mm"
include "ineq1d.mm"
include "sylib.mm"
include "aomclem7.mm"

theorem aomclem8
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vl: setvar l
  assume aomclem8.a: |- ( ph -> A e. On )
  assume aomclem8.y: |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) -> ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) )

  disjoint b ph
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a y
  disjoint b y
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint i ph
  disjoint j ph
  disjoint l ph
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint c j
  disjoint c l
  disjoint b c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint d j
  disjoint d l
  disjoint b d
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e i
  disjoint e j
  disjoint e l
  disjoint b e
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f j
  disjoint f l
  disjoint b f
  disjoint g h
  disjoint g i
  disjoint g j
  disjoint g l
  disjoint b g
  disjoint h i
  disjoint h j
  disjoint h l
  disjoint b h
  disjoint i j
  disjoint i l
  disjoint b i
  disjoint j l
  disjoint b j
  disjoint b l
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A i
  disjoint A j
  disjoint A l
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint a j
  disjoint a l
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint i y
  disjoint j y
  disjoint l y
  assert |- ( ph -> E. b b We ( R1 ` A ) )

  proof
    wph
    vy
    ve
    cA
    vi
    vh
    wel
    #
    vi
    vg
    wel
    #
    wn
    #
    wa
    #
    vj
    cv
    #
    vi
    cv
    #
    ve
    cv
    #
    cdm
    #
    cuni
    #
    @6
    cfv
    #
    wbr
    #
    vj
    vg
    wel
    #
    vj
    vh
    wel
    #
    wb
    #
    wi
    #
    vj
    @8
    cr1
    cfv
    #
    wral
    #
    wa
    #
    vi
    @15
    wrex
    #
    vg
    vh
    copab
    #
    vg
    cvv
    vg
    cv
    #
    vy
    cv
    #
    cfv
    #
    @7
    cr1
    cfv
    #
    @19
    csup
    #
    cmpt
    #
    vg
    cvv
    @23
    @20
    crn
    #
    cdif
    #
    @25
    cfv
    #
    cmpt
    #
    crecs
    #
    @30
    ccnv
    #
    @20
    csn
    #
    cima
    #
    cint
    #
    @31
    vh
    cv
    #
    csn
    #
    cima
    #
    cint
    #
    wcel
    #
    vg
    vh
    copab
    #
    @20
    crnk
    cfv
    #
    @35
    crnk
    cfv
    #
    cep
    wbr
    #
    @41
    @42
    wceq
    #
    @20
    @35
    @41
    csuc
    #
    @6
    cfv
    #
    wbr
    #
    wa
    #
    wo
    #
    vg
    vh
    copab
    #
    @7
    @8
    wceq
    #
    @50
    @40
    cif
    #
    @23
    @23
    cxp
    #
    cin
    #
    vl
    cvv
    vl
    cv
    #
    cdm
    #
    @56
    cuni
    #
    wceq
    #
    @43
    @44
    @20
    @35
    @45
    @55
    cfv
    #
    wbr
    #
    wa
    #
    wo
    #
    vg
    vh
    copab
    #
    vg
    cvv
    @56
    cr1
    cfv
    #
    @26
    cdif
    #
    vg
    cvv
    @22
    @64
    @3
    @4
    @5
    @57
    @55
    cfv
    #
    wbr
    #
    @13
    wi
    #
    vj
    @57
    cr1
    cfv
    #
    wral
    #
    wa
    #
    vi
    @69
    wrex
    #
    vg
    vh
    copab
    #
    csup
    #
    cmpt
    #
    cfv
    #
    cmpt
    #
    crecs
    #
    ccnv
    #
    @32
    cima
    #
    cint
    #
    @79
    @36
    cima
    #
    cint
    #
    wcel
    #
    vg
    vh
    copab
    #
    cif
    #
    @64
    @64
    cxp
    #
    cin
    #
    cmpt
    #
    crecs
    #
    vc
    vb
    vd
    vf
    @18
    vd
    vb
    wel
    #
    vd
    vc
    wel
    #
    wn
    #
    wa
    #
    vf
    cv
    #
    vd
    cv
    #
    @9
    wbr
    #
    vf
    vc
    wel
    #
    vf
    vb
    wel
    #
    wb
    #
    wi
    #
    vf
    @15
    wral
    #
    wa
    #
    vd
    @15
    wrex
    #
    vg
    vh
    vc
    vb
    vg
    vc
    weq
    #
    vh
    vb
    weq
    #
    wa
    #
    @18
    vi
    vb
    wel
    #
    vi
    vc
    wel
    #
    wn
    #
    wa
    #
    @10
    vj
    vc
    wel
    #
    vj
    vb
    wel
    #
    wb
    #
    wi
    #
    vj
    @15
    wral
    #
    wa
    #
    vi
    @15
    wrex
    @104
    @107
    @17
    @117
    vi
    @15
    @107
    @3
    @111
    @16
    @116
    @106
    @0
    @108
    @105
    @2
    @110
    vh
    vb
    vi
    elequ2
    @105
    @1
    @109
    vg
    vc
    vi
    elequ2
    notbid
    bi2anan9r
    @107
    @14
    @115
    vj
    @15
    @107
    @13
    @114
    @10
    @105
    @11
    @112
    @106
    @12
    @113
    vg
    vc
    vj
    elequ2
    vh
    vb
    vj
    elequ2
    bi2bian9
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    @117
    @103
    vi
    vd
    @15
    vi
    vd
    weq
    #
    @111
    @94
    @116
    @102
    @118
    @108
    @91
    @110
    @93
    vi
    vd
    vb
    elequ1
    @118
    @109
    @92
    vi
    vd
    vc
    elequ1
    notbid
    anbi12d
    @118
    @116
    @4
    @96
    @9
    wbr
    #
    @114
    wi
    #
    vj
    @15
    wral
    @102
    @118
    @115
    @120
    vj
    @15
    @118
    @10
    @119
    @114
    @5
    @96
    @4
    @9
    breq2
    imbi1d
    ralbidv
    @120
    @101
    vj
    vf
    @15
    vj
    vf
    weq
    #
    @119
    @97
    @114
    @100
    @4
    @95
    @96
    @9
    breq1
    @121
    @112
    @98
    @113
    @99
    vj
    vf
    vc
    elequ1
    vj
    vf
    vb
    elequ1
    bibi12d
    imbi12d
    cbvralv
    syl6bb
    anbi12d
    cbvrexv
    syl6bb
    cbvopabv
    vg
    vc
    cvv
    @24
    vc
    cv
    #
    @21
    cfv
    #
    @23
    @19
    csup
    vc
    @24
    nfcv
    vg
    @123
    @23
    @19
    vg
    @123
    nfcv
    vg
    @23
    nfcv
    @18
    vg
    vh
    nfopab1
    nfsup
    @105
    @23
    @22
    @123
    @19
    @20
    @122
    @21
    fveq2
    supeq1d
    cbvmpt
    @29
    vc
    cvv
    @23
    @122
    crn
    #
    cdif
    #
    @25
    cfv
    #
    cmpt
    #
    wceq
    @30
    @127
    crecs
    wceq
    vg
    vc
    cvv
    @28
    @126
    vc
    @28
    nfcv
    vg
    cvv
    @24
    @125
    nffvmpt1
    @105
    @27
    @125
    @25
    @105
    @26
    @124
    @23
    @20
    @122
    rneq
    difeq2d
    fveq2d
    cbvmpt
    @29
    @127
    recseq
    ax-mp
    @39
    @31
    @122
    csn
    #
    cima
    #
    cint
    #
    @31
    vb
    cv
    #
    csn
    #
    cima
    #
    cint
    #
    wcel
    #
    vg
    vh
    vc
    vb
    @39
    vc
    nfv
    @39
    vb
    nfv
    vg
    @130
    @134
    vg
    @129
    vg
    @31
    @128
    vg
    @30
    vg
    @29
    vg
    cvv
    @28
    nfmpt1
    nfrecs
    nfcnv
    #
    vg
    @128
    nfcv
    nfima
    nfint
    vg
    @133
    vg
    @31
    @132
    @136
    vg
    @132
    nfcv
    nfima
    nfint
    nfel
    vh
    @130
    @134
    vh
    @129
    vh
    @31
    @128
    vh
    @30
    vh
    @29
    vh
    vg
    cvv
    @28
    vh
    cvv
    nfcv
    #
    vh
    @27
    @25
    vh
    vg
    cvv
    @24
    @137
    vh
    @22
    @23
    @19
    vh
    @22
    nfcv
    vh
    @23
    nfcv
    @18
    vg
    vh
    nfopab2
    nfsup
    nfmpt
    vh
    @27
    nfcv
    nffv
    nfmpt
    nfrecs
    nfcnv
    #
    vh
    @128
    nfcv
    nfima
    nfint
    vh
    @133
    vh
    @31
    @132
    @138
    vh
    @132
    nfcv
    nfima
    nfint
    nfel
    @105
    @34
    @130
    wceq
    @38
    @134
    wceq
    @39
    @135
    wb
    @106
    @105
    @33
    @129
    @105
    @32
    @128
    @31
    @20
    @122
    sneq
    imaeq2d
    inteqd
    @106
    @37
    @133
    @106
    @36
    @132
    @31
    @35
    @131
    sneq
    imaeq2d
    inteqd
    @34
    @130
    @38
    @134
    eleq12
    syl2an
    cbvopab
    @49
    @122
    crnk
    cfv
    #
    @131
    crnk
    cfv
    #
    cep
    wbr
    #
    @139
    @140
    wceq
    #
    @122
    @131
    @139
    csuc
    #
    @6
    cfv
    #
    wbr
    #
    wa
    #
    wo
    vg
    vh
    vc
    vb
    @107
    @43
    @141
    @48
    @146
    @105
    @106
    @41
    @139
    @42
    @140
    cep
    @20
    @122
    crnk
    fveq2
    #
    @35
    @131
    crnk
    fveq2
    #
    breqan12d
    @107
    @44
    @142
    @47
    @145
    @105
    @106
    @41
    @139
    @42
    @140
    @147
    @148
    eqeqan12d
    @107
    @20
    @122
    @35
    @131
    @46
    @144
    @105
    @106
    simpl
    @107
    @45
    @143
    @6
    @105
    @45
    @143
    wceq
    #
    @106
    @105
    @41
    @139
    wceq
    @149
    @147
    @41
    @139
    suceq
    syl
    adantr
    fveq2d
    @105
    @106
    simpr
    breq123d
    anbi12d
    orbi12d
    cbvopabv
    @54
    eqid
    @89
    ve
    cvv
    @54
    cmpt
    #
    wceq
    @90
    @150
    crecs
    wceq
    vl
    ve
    cvv
    @88
    @54
    vl
    ve
    weq
    #
    @86
    @52
    @87
    @53
    @151
    @58
    @51
    @63
    @85
    @50
    @40
    @151
    @56
    @7
    @57
    @8
    @55
    @6
    dmeq
    #
    @151
    @56
    @7
    @152
    unieqd
    #
    eqeq12d
    @151
    @62
    @49
    vg
    vh
    @151
    @61
    @48
    @43
    @151
    @60
    @47
    @44
    @151
    @59
    @46
    @20
    @35
    @45
    @55
    @6
    fveq1
    breqd
    anbi2d
    orbi2d
    opabbidv
    @151
    @84
    @39
    vg
    vh
    @151
    @81
    @34
    @83
    @38
    @151
    @80
    @33
    @151
    @79
    @31
    @32
    @151
    @78
    @30
    @151
    @77
    @29
    wceq
    @78
    @30
    wceq
    @151
    vg
    cvv
    @76
    @28
    @151
    @65
    @27
    @75
    @25
    @151
    vg
    cvv
    @74
    @24
    @151
    @22
    @64
    @73
    @22
    @23
    @19
    @151
    @22
    eqidd
    @151
    @56
    @7
    cr1
    @152
    fveq2d
    #
    @151
    @72
    @18
    vg
    vh
    @151
    @71
    @17
    vi
    @69
    @15
    @151
    @57
    @8
    cr1
    @153
    fveq2d
    #
    @151
    @70
    @16
    @3
    @151
    @68
    @14
    vj
    @69
    @15
    @155
    @151
    @67
    @10
    @13
    @151
    @66
    @9
    @4
    @5
    @151
    @57
    @8
    @55
    @6
    @151
    id
    @153
    fveq12d
    breqd
    imbi1d
    raleqbidv
    anbi2d
    rexeqbidv
    opabbidv
    supeq123d
    mpteq2dv
    @151
    @64
    @23
    @26
    @154
    difeq1d
    fveq12d
    mpteq2dv
    @77
    @29
    recseq
    syl
    cnveqd
    #
    imaeq1d
    inteqd
    @151
    @82
    @37
    @151
    @79
    @31
    @36
    @156
    imaeq1d
    inteqd
    eleq12d
    opabbidv
    ifbieq12d
    @151
    @64
    @23
    @154
    sqxpeqd
    ineq12d
    cbvmptv
    @89
    @150
    recseq
    ax-mp
    aomclem8.a
    wph
    va
    cv
    #
    c0
    wne
    #
    @157
    @21
    cfv
    #
    @157
    cpw
    #
    cfn
    cin
    #
    c0
    csn
    #
    cdif
    #
    wcel
    #
    wi
    #
    va
    cA
    cr1
    cfv
    cpw
    #
    wral
    @122
    c0
    wne
    #
    @123
    @122
    cpw
    #
    cfn
    cin
    #
    @162
    cdif
    #
    wcel
    #
    wi
    #
    vc
    @166
    wral
    aomclem8.y
    @165
    @172
    va
    vc
    @166
    va
    vc
    weq
    #
    @158
    @167
    @164
    @171
    @157
    @122
    c0
    neeq1
    @173
    @159
    @123
    @163
    @170
    @157
    @122
    @21
    fveq2
    @173
    @161
    @169
    @162
    @173
    @160
    @168
    cfn
    @157
    @122
    pweq
    ineq1d
    difeq1d
    eleq12d
    imbi12d
    cbvralv
    sylib
    aomclem7
end
