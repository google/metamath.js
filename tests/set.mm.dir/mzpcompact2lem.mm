include "cmzp.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cfn.mm"
include "wtru.mm"
include "tru.mm"
include "csn.mm"
include "cxp.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "c0.mm"
include "0fin.mm"
include "cvv.mm"
include "0ex.mm"
include "mzpconst.mm"
include "mpan.mm"
include "0ss.mm"
include "a1i.mm"
include "simpr.mm"
include "elmapssres.mm"
include "sylancl.mm"
include "vex.mm"
include "fvconst2.mm"
include "syl.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6reqr.mm"
include "fveq1.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "fveq2.mm"
include "sseq1.mm"
include "reseq2.mm"
include "fveq2d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "sylancr.mm"
include "adantl.mm"
include "snfi.mm"
include "snex.mm"
include "vsnid.mm"
include "mzpproj.mm"
include "mp2an.mm"
include "snssi.mm"
include "cbvmptv.mm"
include "simpl.mm"
include "snssd.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "fvres.mm"
include "ax-mp.mm"
include "syl6req.mm"
include "syl5eq.mm"
include "wf.mm"
include "w3a.mm"
include "wi.mm"
include "cun.mm"
include "simplll.mm"
include "simprll.mm"
include "unfi.mm"
include "unex.mm"
include "ssun1.mm"
include "simpllr.mm"
include "mzpresrename.mm"
include "syl3anc.mm"
include "ssun2.mm"
include "simprlr.mm"
include "mzpaddmpt.mm"
include "simplr.mm"
include "simprr.mm"
include "unssd.mm"
include "wfn.mm"
include "ovex.mm"
include "mzpf.mm"
include "ffn.mm"
include "3syl.mm"
include "ofmpteq.mm"
include "elmapi.mm"
include "fssres.mm"
include "syl2anr.mm"
include "zex.mm"
include "elmap.mm"
include "sylibr.mm"
include "reseq1.mm"
include "oveq12d.mm"
include "resabs1.mm"
include "fveq2i.mm"
include "oveq12i.mm"
include "eqtrd.mm"
include "mzpmulmpt.mm"
include "adantlrr.mm"
include "adantrrr.mm"
include "simplrr.mm"
include "simprrr.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "r19.40.mm"
include "exp32.mm"
include "rexlimdvv.mm"
include "ex.mm"
include "rexlimivv.mm"
include "imp.mm"
include "ad2ant2l.mm"
include "3adant1.mm"
include "simpld.mm"
include "simprd.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "weq.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "mzpindd.mm"
include "eqeq2i.mm"
include "anbi2i.mm"
include "2rexbii.mm"
include "sylib.mm"

theorem mzpcompact2lem
  let cA: class A
  let cB: class B
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
  let vk: setvar k
  let vl: setvar l
  assume mzpcompact2lem.i: |- B e. _V

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a c
  disjoint b c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint A l
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a l
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d l
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e l
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint g h
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g l
  disjoint h i
  disjoint h j
  disjoint h k
  disjoint h l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c l
  assert |- ( A e. ( mzPoly ` B ) -> E. a e. Fin E. b e. ( mzPoly ` a ) ( a C_ B /\ A = ( c e. ( ZZ ^m B ) |-> ( b ` ( c |` a ) ) ) ) )

  proof
    cA
    cB
    cmzp
    cfv
    #
    wcel
    #
    va
    cv
    #
    cB
    wss
    #
    cA
    vd
    cz
    cB
    cmap
    co
    #
    vd
    cv
    #
    @2
    cres
    #
    vb
    cv
    #
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    @2
    cmzp
    cfv
    #
    wrex
    va
    cfn
    wrex
    #
    @3
    cA
    vc
    @4
    vc
    cv
    #
    @2
    cres
    #
    @7
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    va
    cfn
    wrex
    wtru
    @1
    @13
    tru
    wtru
    @3
    ve
    cv
    #
    @9
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    va
    cfn
    wrex
    #
    @3
    @4
    vf
    cv
    #
    csn
    #
    cxp
    #
    @9
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    va
    cfn
    wrex
    #
    @3
    vg
    @4
    @24
    vg
    cv
    #
    cfv
    #
    cmpt
    #
    @9
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    va
    cfn
    wrex
    #
    vh
    cv
    #
    cB
    wss
    #
    @24
    vd
    @4
    @5
    @38
    cres
    #
    vi
    cv
    #
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vi
    @38
    cmzp
    cfv
    #
    wrex
    #
    vh
    cfn
    wrex
    #
    vj
    cv
    #
    cB
    wss
    #
    @31
    vd
    @4
    @5
    @49
    cres
    #
    vk
    cv
    #
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vk
    @49
    cmzp
    cfv
    #
    wrex
    #
    vj
    cfn
    wrex
    #
    @3
    @24
    @31
    caddc
    cof
    #
    co
    #
    @9
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    va
    cfn
    wrex
    #
    @3
    @24
    @31
    cmul
    cof
    #
    co
    #
    @9
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    va
    cfn
    wrex
    #
    @13
    ve
    cA
    vf
    vg
    cB
    @24
    cz
    wcel
    #
    @30
    wtru
    @72
    c0
    cfn
    wcel
    c0
    cB
    wss
    #
    @26
    vd
    @4
    @5
    c0
    cres
    #
    @7
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    c0
    cmzp
    cfv
    #
    wrex
    #
    @30
    0fin
    @72
    cz
    c0
    cmap
    co
    #
    @25
    cxp
    #
    @79
    wcel
    #
    @73
    @26
    vd
    @4
    @74
    @82
    cfv
    #
    cmpt
    #
    wceq
    #
    @80
    c0
    cvv
    wcel
    @72
    @83
    0ex
    @24
    c0
    mzpconst
    mpan
    @73
    @72
    cB
    0ss
    #
    a1i
    @72
    @85
    vd
    @4
    @24
    cmpt
    @26
    @72
    vd
    @4
    @84
    @24
    @72
    @5
    @4
    wcel
    #
    wa
    #
    @74
    @81
    wcel
    #
    @84
    @24
    wceq
    @89
    @88
    @73
    @90
    @72
    @88
    simpr
    @87
    @5
    cz
    cB
    c0
    elmapssres
    sylancl
    @81
    @24
    @74
    vf
    vex
    fvconst2
    syl
    mpteq2dva
    vd
    @4
    @24
    fconstmpt
    syl6reqr
    @78
    @73
    @86
    wa
    vb
    @82
    @79
    @7
    @82
    wceq
    #
    @77
    @86
    @73
    @91
    @76
    @85
    @26
    @91
    vd
    @4
    @75
    @84
    @74
    @7
    @82
    fveq1
    mpteq2dv
    eqeq2d
    anbi2d
    rspcev
    syl12anc
    @29
    @80
    va
    c0
    cfn
    @2
    c0
    wceq
    #
    @28
    @78
    vb
    @12
    @79
    @2
    c0
    cmzp
    fveq2
    @92
    @3
    @73
    @27
    @77
    @2
    c0
    cB
    sseq1
    @92
    @9
    @76
    @26
    @92
    vd
    @4
    @8
    @75
    @92
    @6
    @74
    @7
    @2
    c0
    @5
    reseq2
    fveq2d
    mpteq2dv
    eqeq2d
    anbi12d
    rexeqbidv
    rspcev
    sylancr
    adantl
    @24
    cB
    wcel
    #
    @37
    wtru
    @93
    @25
    cfn
    wcel
    @25
    cB
    wss
    #
    @33
    vd
    @4
    @5
    @25
    cres
    #
    @7
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    @25
    cmzp
    cfv
    #
    wrex
    #
    @37
    @24
    snfi
    @93
    vg
    cz
    @25
    cmap
    co
    #
    @32
    cmpt
    #
    @100
    wcel
    #
    @94
    @33
    vd
    @4
    @95
    @103
    cfv
    #
    cmpt
    #
    wceq
    #
    @101
    @104
    @93
    @25
    cvv
    wcel
    @24
    @25
    wcel
    #
    @104
    @24
    snex
    vf
    vsnid
    #
    vg
    @25
    @24
    mzpproj
    mp2an
    a1i
    @24
    cB
    snssi
    @93
    @33
    vd
    @4
    @24
    @5
    cfv
    #
    cmpt
    @106
    vg
    vd
    @4
    @32
    @110
    @24
    @31
    @5
    fveq1
    cbvmptv
    @93
    vd
    @4
    @110
    @105
    @93
    @88
    wa
    #
    @105
    @24
    @95
    cfv
    #
    @110
    @111
    @95
    @102
    wcel
    #
    @105
    @112
    wceq
    @111
    @88
    @94
    @113
    @93
    @88
    simpr
    @111
    @24
    cB
    @93
    @88
    simpl
    snssd
    @5
    cz
    cB
    @25
    elmapssres
    syl2anc
    vg
    @95
    @32
    @112
    @102
    @103
    @24
    @31
    @95
    fveq1
    @103
    eqid
    @24
    @95
    fvex
    fvmpt
    syl
    @108
    @112
    @110
    wceq
    @109
    @24
    @25
    @5
    fvres
    ax-mp
    syl6req
    mpteq2dva
    syl5eq
    @99
    @94
    @107
    wa
    vb
    @103
    @100
    @7
    @103
    wceq
    #
    @98
    @107
    @94
    @114
    @97
    @106
    @33
    @114
    vd
    @4
    @96
    @105
    @95
    @7
    @103
    fveq1
    mpteq2dv
    eqeq2d
    anbi2d
    rspcev
    syl12anc
    @36
    @101
    va
    @25
    cfn
    @2
    @25
    wceq
    #
    @35
    @99
    vb
    @12
    @100
    @2
    @25
    cmzp
    fveq2
    @115
    @3
    @94
    @34
    @98
    @2
    @25
    cB
    sseq1
    @115
    @9
    @97
    @33
    @115
    vd
    @4
    @8
    @96
    @115
    @6
    @95
    @7
    @2
    @25
    @5
    reseq2
    fveq2d
    mpteq2dv
    eqeq2d
    anbi12d
    rexeqbidv
    rspcev
    sylancr
    adantl
    wtru
    @4
    cz
    @24
    wf
    #
    @48
    wa
    #
    @4
    cz
    @31
    wf
    #
    @59
    wa
    #
    w3a
    #
    @65
    @71
    @117
    @119
    @65
    @71
    wa
    #
    wtru
    @48
    @59
    @121
    @116
    @118
    @48
    @59
    @121
    @45
    @59
    @121
    wi
    #
    vh
    vi
    cfn
    @46
    @38
    cfn
    wcel
    #
    @41
    @46
    wcel
    #
    wa
    #
    @45
    @122
    @125
    @45
    wa
    #
    @56
    @121
    vj
    vk
    cfn
    @57
    @126
    @49
    cfn
    wcel
    #
    @52
    @57
    wcel
    #
    wa
    #
    @56
    @121
    @126
    @129
    @56
    wa
    #
    wa
    #
    @64
    @70
    wa
    #
    va
    cfn
    wrex
    #
    @121
    @131
    @133
    @3
    @43
    @54
    @60
    co
    #
    @9
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    @3
    @43
    @54
    @66
    co
    #
    @9
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    wa
    #
    va
    cfn
    wrex
    #
    @126
    @129
    @50
    @143
    @55
    @125
    @39
    @129
    @50
    wa
    #
    @143
    @44
    @125
    @39
    wa
    #
    @144
    wa
    #
    @38
    @49
    cun
    #
    cfn
    wcel
    #
    @147
    cB
    wss
    #
    @134
    vd
    @4
    @5
    @147
    cres
    #
    @7
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    @147
    cmzp
    cfv
    #
    wrex
    #
    @149
    @138
    @152
    wceq
    #
    wa
    #
    vb
    @155
    wrex
    #
    @143
    @146
    @123
    @127
    @148
    @123
    @124
    @39
    @144
    simplll
    @145
    @127
    @128
    @50
    simprll
    @38
    @49
    unfi
    syl2anc
    @146
    vl
    cz
    @147
    cmap
    co
    #
    vl
    cv
    #
    @38
    cres
    #
    @41
    cfv
    #
    @161
    @49
    cres
    #
    @52
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    @155
    wcel
    #
    @149
    @134
    vd
    @4
    @150
    @167
    cfv
    #
    cmpt
    #
    wceq
    #
    @156
    @146
    vl
    @160
    @163
    cmpt
    @155
    wcel
    #
    vl
    @160
    @165
    cmpt
    @155
    wcel
    #
    @168
    @146
    @147
    cvv
    wcel
    #
    @38
    @147
    wss
    #
    @124
    @172
    @174
    @146
    @38
    @49
    vh
    vex
    vj
    vex
    unex
    #
    a1i
    #
    @175
    @146
    @38
    @49
    ssun1
    #
    a1i
    @123
    @124
    @39
    @144
    simpllr
    #
    vl
    @41
    @38
    @147
    mzpresrename
    syl3anc
    #
    @146
    @174
    @49
    @147
    wss
    #
    @128
    @173
    @177
    @181
    @146
    @49
    @38
    ssun2
    #
    a1i
    @145
    @127
    @128
    @50
    simprlr
    #
    vl
    @52
    @49
    @147
    mzpresrename
    syl3anc
    #
    vl
    @163
    @165
    @147
    mzpaddmpt
    syl2anc
    @146
    @38
    @49
    cB
    @125
    @39
    @144
    simplr
    #
    @145
    @129
    @50
    simprr
    #
    unssd
    #
    @146
    @134
    vd
    @4
    @42
    @53
    caddc
    co
    #
    cmpt
    #
    @170
    @146
    @4
    cvv
    wcel
    #
    @43
    @4
    wfn
    #
    @54
    @4
    wfn
    #
    @134
    @189
    wceq
    @190
    @146
    cz
    cB
    cmap
    ovex
    a1i
    #
    @146
    @43
    @0
    wcel
    #
    @4
    cz
    @43
    wf
    @191
    @146
    cB
    cvv
    wcel
    #
    @39
    @124
    @194
    @195
    @146
    mzpcompact2lem.i
    a1i
    #
    @185
    @179
    vd
    @41
    @38
    cB
    mzpresrename
    syl3anc
    @43
    cB
    mzpf
    @4
    cz
    @43
    ffn
    3syl
    #
    @146
    @54
    @0
    wcel
    #
    @4
    cz
    @54
    wf
    @192
    @146
    @195
    @50
    @128
    @198
    @196
    @186
    @183
    vd
    @52
    @49
    cB
    mzpresrename
    syl3anc
    @54
    cB
    mzpf
    @4
    cz
    @54
    ffn
    3syl
    #
    vd
    @4
    @42
    @53
    caddc
    cvv
    ofmpteq
    syl3anc
    @146
    vd
    @4
    @188
    @169
    @146
    @88
    wa
    #
    @169
    @150
    @38
    cres
    #
    @41
    cfv
    #
    @150
    @49
    cres
    #
    @52
    cfv
    #
    caddc
    co
    #
    @188
    @200
    @150
    @160
    wcel
    #
    @169
    @205
    wceq
    @200
    @147
    cz
    @150
    wf
    #
    @206
    @88
    cB
    cz
    @5
    wf
    @149
    @207
    @146
    @5
    cz
    cB
    elmapi
    @187
    cB
    cz
    @147
    @5
    fssres
    syl2anr
    cz
    @147
    @150
    zex
    @176
    elmap
    sylibr
    #
    vl
    @150
    @166
    @205
    @160
    @167
    @161
    @150
    wceq
    #
    @163
    @202
    @165
    @204
    caddc
    @209
    @162
    @201
    @41
    @161
    @150
    @38
    reseq1
    fveq2d
    #
    @209
    @164
    @203
    @52
    @161
    @150
    @49
    reseq1
    fveq2d
    #
    oveq12d
    @167
    eqid
    @202
    @204
    caddc
    ovex
    fvmpt
    syl
    @202
    @42
    @204
    @53
    caddc
    @201
    @40
    @41
    @175
    @201
    @40
    wceq
    @178
    @5
    @38
    @147
    resabs1
    ax-mp
    fveq2i
    #
    @203
    @51
    @52
    @181
    @203
    @51
    wceq
    @182
    @5
    @49
    @147
    resabs1
    ax-mp
    fveq2i
    #
    oveq12i
    syl6req
    mpteq2dva
    eqtrd
    @154
    @149
    @171
    wa
    vb
    @167
    @155
    @7
    @167
    wceq
    #
    @153
    @171
    @149
    @214
    @152
    @170
    @134
    @214
    vd
    @4
    @151
    @169
    @150
    @7
    @167
    fveq1
    mpteq2dv
    eqeq2d
    anbi2d
    rspcev
    syl12anc
    @146
    vl
    @160
    @163
    @165
    cmul
    co
    #
    cmpt
    #
    @155
    wcel
    #
    @149
    @138
    vd
    @4
    @150
    @216
    cfv
    #
    cmpt
    #
    wceq
    #
    @159
    @146
    @172
    @173
    @217
    @180
    @184
    vl
    @163
    @165
    @147
    mzpmulmpt
    syl2anc
    @187
    @146
    @138
    vd
    @4
    @42
    @53
    cmul
    co
    #
    cmpt
    #
    @219
    @146
    @190
    @191
    @192
    @138
    @222
    wceq
    @193
    @197
    @199
    vd
    @4
    @42
    @53
    cmul
    cvv
    ofmpteq
    syl3anc
    @146
    vd
    @4
    @221
    @218
    @200
    @218
    @202
    @204
    cmul
    co
    #
    @221
    @200
    @206
    @218
    @223
    wceq
    @208
    vl
    @150
    @215
    @223
    @160
    @216
    @209
    @163
    @202
    @165
    @204
    cmul
    @210
    @211
    oveq12d
    @216
    eqid
    @202
    @204
    cmul
    ovex
    fvmpt
    syl
    @202
    @42
    @204
    @53
    cmul
    @212
    @213
    oveq12i
    syl6req
    mpteq2dva
    eqtrd
    @158
    @149
    @220
    wa
    vb
    @216
    @155
    @7
    @216
    wceq
    #
    @157
    @220
    @149
    @224
    @152
    @219
    @138
    @224
    vd
    @4
    @151
    @218
    @150
    @7
    @216
    fveq1
    mpteq2dv
    eqeq2d
    anbi2d
    rspcev
    syl12anc
    @142
    @156
    @159
    wa
    va
    @147
    cfn
    @2
    @147
    wceq
    #
    @137
    @156
    @141
    @159
    @225
    @136
    @154
    vb
    @12
    @155
    @2
    @147
    cmzp
    fveq2
    #
    @225
    @3
    @149
    @135
    @153
    @2
    @147
    cB
    sseq1
    #
    @225
    @9
    @152
    @134
    @225
    vd
    @4
    @8
    @151
    @225
    @6
    @150
    @7
    @2
    @147
    @5
    reseq2
    fveq2d
    mpteq2dv
    #
    eqeq2d
    anbi12d
    rexeqbidv
    @225
    @140
    @158
    vb
    @12
    @155
    @226
    @225
    @3
    @149
    @139
    @157
    @227
    @225
    @9
    @152
    @138
    @228
    eqeq2d
    anbi12d
    rexeqbidv
    anbi12d
    rspcev
    syl12anc
    adantlrr
    adantrrr
    @131
    @132
    @142
    va
    cfn
    @131
    @64
    @137
    @70
    @141
    @131
    @63
    @136
    vb
    @12
    @131
    @62
    @135
    @3
    @131
    @61
    @134
    @9
    @131
    @24
    @43
    @31
    @54
    @60
    @125
    @39
    @44
    @130
    simplrr
    #
    @126
    @129
    @50
    @55
    simprrr
    #
    oveq12d
    eqeq1d
    anbi2d
    rexbidv
    @131
    @69
    @140
    vb
    @12
    @131
    @68
    @139
    @3
    @131
    @67
    @138
    @9
    @131
    @24
    @43
    @31
    @54
    @66
    @229
    @230
    oveq12d
    eqeq1d
    anbi2d
    rexbidv
    anbi12d
    rexbidv
    mpbird
    @64
    @70
    va
    cfn
    r19.40
    syl
    exp32
    rexlimdvv
    ex
    rexlimivv
    imp
    ad2ant2l
    3adant1
    #
    simpld
    @120
    @65
    @71
    @231
    simprd
    @20
    @26
    wceq
    #
    @22
    @28
    va
    vb
    cfn
    @12
    @232
    @21
    @27
    @3
    @20
    @26
    @9
    eqeq1
    anbi2d
    2rexbidv
    @20
    @33
    wceq
    #
    @22
    @35
    va
    vb
    cfn
    @12
    @233
    @21
    @34
    @3
    @20
    @33
    @9
    eqeq1
    anbi2d
    2rexbidv
    ve
    vf
    weq
    #
    @23
    @3
    @24
    @9
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    va
    cfn
    wrex
    @48
    @234
    @22
    @236
    va
    vb
    cfn
    @12
    @234
    @21
    @235
    @3
    @20
    @24
    @9
    eqeq1
    anbi2d
    2rexbidv
    @237
    @47
    va
    vh
    cfn
    va
    vh
    weq
    #
    @237
    @39
    @24
    vd
    @4
    @40
    @7
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    @46
    wrex
    @47
    @238
    @236
    @242
    vb
    @12
    @46
    @2
    @38
    cmzp
    fveq2
    @238
    @3
    @39
    @235
    @241
    @2
    @38
    cB
    sseq1
    @238
    @9
    @240
    @24
    @238
    vd
    @4
    @8
    @239
    @238
    @6
    @40
    @7
    @2
    @38
    @5
    reseq2
    fveq2d
    mpteq2dv
    eqeq2d
    anbi12d
    rexeqbidv
    @242
    @45
    vb
    vi
    @46
    vb
    vi
    weq
    #
    @241
    @44
    @39
    @243
    @240
    @43
    @24
    @243
    vd
    @4
    @239
    @42
    @40
    @7
    @41
    fveq1
    mpteq2dv
    eqeq2d
    anbi2d
    cbvrexv
    syl6bb
    cbvrexv
    syl6bb
    ve
    vg
    weq
    #
    @23
    @3
    @31
    @9
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    va
    cfn
    wrex
    @59
    @244
    @22
    @246
    va
    vb
    cfn
    @12
    @244
    @21
    @245
    @3
    @20
    @31
    @9
    eqeq1
    anbi2d
    2rexbidv
    @247
    @58
    va
    vj
    cfn
    va
    vj
    weq
    #
    @247
    @50
    @31
    vd
    @4
    @51
    @7
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    @57
    wrex
    @58
    @248
    @246
    @252
    vb
    @12
    @57
    @2
    @49
    cmzp
    fveq2
    @248
    @3
    @50
    @245
    @251
    @2
    @49
    cB
    sseq1
    @248
    @9
    @250
    @31
    @248
    vd
    @4
    @8
    @249
    @248
    @6
    @51
    @7
    @2
    @49
    @5
    reseq2
    fveq2d
    mpteq2dv
    eqeq2d
    anbi12d
    rexeqbidv
    @252
    @56
    vb
    vk
    @57
    vb
    vk
    weq
    #
    @251
    @55
    @50
    @253
    @250
    @54
    @31
    @253
    vd
    @4
    @249
    @53
    @51
    @7
    @52
    fveq1
    mpteq2dv
    eqeq2d
    anbi2d
    cbvrexv
    syl6bb
    cbvrexv
    syl6bb
    @20
    @61
    wceq
    #
    @22
    @63
    va
    vb
    cfn
    @12
    @254
    @21
    @62
    @3
    @20
    @61
    @9
    eqeq1
    anbi2d
    2rexbidv
    @20
    @67
    wceq
    #
    @22
    @69
    va
    vb
    cfn
    @12
    @255
    @21
    @68
    @3
    @20
    @67
    @9
    eqeq1
    anbi2d
    2rexbidv
    @20
    cA
    wceq
    #
    @22
    @11
    va
    vb
    cfn
    @12
    @256
    @21
    @10
    @3
    @20
    cA
    @9
    eqeq1
    anbi2d
    2rexbidv
    mzpindd
    mpan
    @11
    @19
    va
    vb
    cfn
    @12
    @10
    @18
    @3
    @9
    @17
    cA
    vd
    vc
    @4
    @8
    @16
    vd
    vc
    weq
    @6
    @15
    @7
    @5
    @14
    @2
    reseq1
    fveq2d
    cbvmptv
    eqeq2i
    anbi2i
    2rexbii
    sylib
end
