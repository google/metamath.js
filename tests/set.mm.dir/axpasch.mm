include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "cc0.mm"
include "cicc.mm"
include "wrex.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wi.mm"
include "axpaschlem.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "oveq1d.mm"
include "eqcomd.mm"
include "simp2.mm"
include "oveq12d.mm"
include "simp3.mm"
include "adantr.mm"
include "cr.mm"
include "1re.mm"
include "simpl2l.mm"
include "cle.mm"
include "0re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "syl.mm"
include "resubcl.mm"
include "sylancr.mm"
include "recnd.mm"
include "simp13l.mm"
include "simp121.mm"
include "fveere.mm"
include "sylan.mm"
include "remulcld.mm"
include "simp123.mm"
include "adddid.mm"
include "mulassd.mm"
include "cc.mm"
include "fveecn.mm"
include "eqtr4d.mm"
include "simp122.mm"
include "add32d.mm"
include "eqtrd.mm"
include "simpl2r.mm"
include "simp13r.mm"
include "oveq2d.mm"
include "comraddd.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "3expia.mm"
include "reximdvva.mm"
include "mpd.mm"
include "cmpt.mm"
include "simplrl.mm"
include "simpl3l.mm"
include "simpl21.mm"
include "simpl23.mm"
include "readdcld.mm"
include "simpl22.mm"
include "anassrs.mm"
include "wb.mm"
include "simpll1.mm"
include "mptelee.mm"
include "mpbird.mm"
include "fveq1.mm"
include "fveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "biantrur.mm"
include "syl6bbr.mm"
include "ralbidva.mm"
include "rspcev.mm"
include "ex.mm"
include "reximdva.mm"
include "rexcom.mm"
include "rexbii.mm"
include "bitri.mm"
include "sylib.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "bi2anan9.mm"
include "ralimi.mm"
include "ralbi.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdvv.mm"
include "3adant3.mm"
include "simp3l.mm"
include "simp21.mm"
include "simp23.mm"
include "brbtwn.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "simp22.mm"
include "r19.26.mm"
include "2rexbii.mm"
include "reeanv.mm"
include "simpr.mm"
include "simpl3r.mm"
include "rexbidva.mm"
include "3imtr4d.mm"

theorem axpasch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cN: class N
  let vi: setvar i
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint E x
  disjoint N x
  disjoint A i
  disjoint A q
  disjoint A r
  disjoint B i
  disjoint B q
  disjoint B r
  disjoint C i
  disjoint C q
  disjoint C r
  disjoint i q
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint N i
  disjoint N q
  disjoint N r
  disjoint q r
  disjoint q s
  disjoint q t
  disjoint r s
  disjoint r t
  disjoint A s
  disjoint A t
  disjoint B s
  disjoint B t
  disjoint C s
  disjoint C t
  disjoint D i
  disjoint D q
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint E i
  disjoint E q
  disjoint E r
  disjoint E s
  disjoint E t
  disjoint i x
  disjoint N s
  disjoint N t
  disjoint q x
  disjoint r x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint i k
  disjoint k q
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint N k
  disjoint D k
  disjoint E k
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) -> ( ( D Btwn <. A , C >. /\ E Btwn <. B , C >. ) -> E. x e. ( EE ` N ) ( x Btwn <. D , B >. /\ x Btwn <. E , A >. ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    wa
    #
    w3a
    #
    vi
    cv
    #
    cD
    cfv
    #
    c1
    vt
    cv
    #
    cmin
    co
    #
    @10
    cA
    cfv
    #
    cmul
    co
    #
    @12
    @10
    cC
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @10
    cE
    cfv
    #
    c1
    vs
    cv
    #
    cmin
    co
    #
    @10
    cB
    cfv
    #
    cmul
    co
    #
    @21
    @16
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    vs
    cc0
    c1
    cicc
    co
    #
    wrex
    vt
    @31
    wrex
    #
    @10
    vx
    cv
    #
    cfv
    #
    c1
    vr
    cv
    #
    cmin
    co
    #
    @11
    cmul
    co
    #
    @35
    @23
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @34
    c1
    vq
    cv
    #
    cmin
    co
    #
    @20
    cmul
    co
    #
    @41
    @14
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vi
    @29
    wral
    #
    vq
    @31
    wrex
    #
    vr
    @31
    wrex
    #
    vx
    @1
    wrex
    #
    cD
    cA
    cC
    cop
    cbtwn
    wbr
    #
    cE
    cB
    cC
    cop
    cbtwn
    wbr
    #
    wa
    #
    @33
    cD
    cB
    cop
    cbtwn
    wbr
    #
    @33
    cE
    cA
    cop
    cbtwn
    wbr
    #
    wa
    #
    vx
    @1
    wrex
    @0
    @5
    @32
    @51
    wi
    @8
    @0
    @5
    wa
    @30
    @51
    vt
    vs
    @31
    @31
    @0
    @5
    @12
    @31
    wcel
    #
    @21
    @31
    wcel
    #
    wa
    #
    @30
    @51
    wi
    @0
    @5
    @60
    w3a
    #
    @51
    @30
    @34
    @36
    @18
    cmul
    co
    #
    @38
    caddc
    co
    #
    wceq
    #
    @34
    @42
    @26
    cmul
    co
    #
    @44
    caddc
    co
    #
    wceq
    #
    wa
    #
    vi
    @29
    wral
    #
    vq
    @31
    wrex
    #
    vr
    @31
    wrex
    vx
    @1
    wrex
    #
    @61
    @69
    vx
    @1
    wrex
    #
    vq
    @31
    wrex
    #
    vr
    @31
    wrex
    #
    @71
    @61
    @63
    @66
    wceq
    #
    vi
    @29
    wral
    #
    vq
    @31
    wrex
    #
    vr
    @31
    wrex
    #
    @74
    @61
    @41
    @36
    @13
    cmul
    co
    #
    wceq
    #
    @35
    @42
    @22
    cmul
    co
    #
    wceq
    #
    @36
    @12
    cmul
    co
    #
    @42
    @21
    cmul
    co
    #
    wceq
    #
    w3a
    #
    vq
    @31
    wrex
    vr
    @31
    wrex
    #
    @78
    @60
    @0
    @87
    @5
    @21
    @12
    vr
    vq
    axpaschlem
    3ad2ant3
    @61
    @86
    @76
    vr
    vq
    @31
    @31
    @61
    @35
    @31
    wcel
    #
    @41
    @31
    wcel
    #
    wa
    #
    @86
    @76
    @61
    @90
    @86
    w3a
    #
    @75
    vi
    @29
    @91
    @10
    @29
    wcel
    #
    wa
    #
    @79
    @14
    cmul
    co
    #
    @38
    caddc
    co
    #
    @83
    @16
    cmul
    co
    #
    caddc
    co
    #
    @44
    @81
    @23
    cmul
    co
    #
    caddc
    co
    #
    @84
    @16
    cmul
    co
    #
    caddc
    co
    #
    @63
    @66
    @91
    @97
    @101
    wceq
    #
    @92
    @86
    @61
    @102
    @90
    @86
    @95
    @99
    @96
    @100
    caddc
    @86
    @94
    @44
    @38
    @98
    caddc
    @86
    @44
    @94
    @86
    @41
    @79
    @14
    cmul
    @80
    @82
    @85
    simp1
    oveq1d
    eqcomd
    @86
    @35
    @81
    @23
    cmul
    @80
    @82
    @85
    simp2
    oveq1d
    oveq12d
    @86
    @83
    @84
    @16
    cmul
    @80
    @82
    @85
    simp3
    oveq1d
    oveq12d
    3ad2ant3
    adantr
    @93
    @63
    @94
    @96
    caddc
    co
    #
    @38
    caddc
    co
    @97
    @93
    @62
    @103
    @38
    caddc
    @93
    @62
    @36
    @15
    cmul
    co
    #
    @36
    @17
    cmul
    co
    #
    caddc
    co
    @103
    @93
    @36
    @15
    @17
    @93
    @36
    @93
    c1
    cr
    wcel
    #
    @35
    cr
    wcel
    #
    @36
    cr
    wcel
    #
    1re
    @93
    @88
    @107
    @88
    @89
    @61
    @86
    @92
    simpl2l
    @88
    @107
    cc0
    @35
    cle
    wbr
    @35
    c1
    cle
    wbr
    cc0
    c1
    @35
    0re
    1re
    elicc2i
    simp1bi
    #
    syl
    #
    c1
    @35
    resubcl
    #
    sylancr
    #
    recnd
    #
    @93
    @15
    @93
    @13
    @14
    @93
    @106
    @12
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    1re
    @93
    @58
    @114
    @91
    @58
    @92
    @58
    @59
    @0
    @5
    @90
    @86
    simp13l
    adantr
    @58
    @114
    cc0
    @12
    cle
    wbr
    @12
    c1
    cle
    wbr
    cc0
    c1
    @12
    0re
    1re
    elicc2i
    simp1bi
    #
    syl
    #
    c1
    @12
    resubcl
    #
    sylancr
    #
    @91
    @2
    @92
    @14
    cr
    wcel
    @2
    @3
    @4
    @0
    @60
    @90
    @86
    simp121
    cA
    @10
    cN
    fveere
    sylan
    #
    remulcld
    recnd
    @93
    @17
    @93
    @12
    @16
    @117
    @91
    @4
    @92
    @16
    cr
    wcel
    @2
    @3
    @4
    @0
    @60
    @90
    @86
    simp123
    #
    cC
    @10
    cN
    fveere
    sylan
    #
    remulcld
    recnd
    adddid
    @93
    @94
    @104
    @96
    @105
    caddc
    @93
    @36
    @13
    @14
    @113
    @93
    @13
    @119
    recnd
    @93
    @14
    @120
    recnd
    mulassd
    @93
    @36
    @12
    @16
    @113
    @93
    @12
    @117
    recnd
    @91
    @4
    @92
    @16
    cc
    wcel
    @121
    cC
    @10
    cN
    fveecn
    sylan
    #
    mulassd
    oveq12d
    eqtr4d
    oveq1d
    @93
    @94
    @96
    @38
    @93
    @94
    @93
    @79
    @14
    @93
    @36
    @13
    @112
    @119
    remulcld
    @120
    remulcld
    recnd
    @93
    @96
    @93
    @83
    @16
    @93
    @36
    @12
    @112
    @117
    remulcld
    @122
    remulcld
    recnd
    @93
    @38
    @93
    @35
    @23
    @110
    @91
    @3
    @92
    @23
    cr
    wcel
    @2
    @3
    @4
    @0
    @60
    @90
    @86
    simp122
    cB
    @10
    cN
    fveere
    sylan
    #
    remulcld
    recnd
    add32d
    eqtrd
    @93
    @42
    @24
    cmul
    co
    #
    @42
    @25
    cmul
    co
    #
    caddc
    co
    #
    @44
    caddc
    co
    @125
    @44
    caddc
    co
    #
    @126
    caddc
    co
    @66
    @101
    @93
    @125
    @126
    @44
    @93
    @125
    @93
    @42
    @24
    @93
    @106
    @41
    cr
    wcel
    #
    @42
    cr
    wcel
    1re
    @93
    @89
    @129
    @88
    @89
    @61
    @86
    @92
    simpl2r
    @89
    @129
    cc0
    @41
    cle
    wbr
    @41
    c1
    cle
    wbr
    cc0
    c1
    @41
    0re
    1re
    elicc2i
    simp1bi
    syl
    #
    c1
    @41
    resubcl
    sylancr
    #
    @93
    @22
    @23
    @93
    @106
    @21
    cr
    wcel
    #
    @22
    cr
    wcel
    1re
    @93
    @59
    @132
    @91
    @59
    @92
    @58
    @59
    @0
    @5
    @90
    @86
    simp13r
    adantr
    @59
    @132
    cc0
    @21
    cle
    wbr
    @21
    c1
    cle
    wbr
    cc0
    c1
    @21
    0re
    1re
    elicc2i
    simp1bi
    syl
    #
    c1
    @21
    resubcl
    sylancr
    #
    @124
    remulcld
    #
    remulcld
    recnd
    #
    @93
    @126
    @93
    @42
    @25
    @131
    @93
    @21
    @16
    @133
    @122
    remulcld
    #
    remulcld
    recnd
    @93
    @44
    @93
    @41
    @14
    @130
    @120
    remulcld
    recnd
    #
    add32d
    @93
    @65
    @127
    @44
    caddc
    @93
    @42
    @24
    @25
    @93
    @42
    @131
    recnd
    #
    @93
    @24
    @135
    recnd
    @93
    @25
    @137
    recnd
    adddid
    oveq1d
    @93
    @99
    @128
    @100
    @126
    caddc
    @93
    @99
    @44
    @125
    @138
    @136
    @93
    @98
    @125
    @44
    caddc
    @93
    @42
    @22
    @23
    @139
    @93
    @22
    @134
    recnd
    @93
    @23
    @124
    recnd
    mulassd
    oveq2d
    comraddd
    @93
    @42
    @21
    @16
    @139
    @93
    @21
    @133
    recnd
    @123
    mulassd
    oveq12d
    3eqtr4d
    3eqtr4d
    ralrimiva
    3expia
    reximdvva
    mpd
    @61
    @77
    @73
    vr
    @31
    @61
    @88
    wa
    #
    @76
    @72
    vq
    @31
    @140
    @89
    wa
    #
    vk
    @29
    @36
    @13
    vk
    cv
    #
    cA
    cfv
    #
    cmul
    co
    #
    @12
    @142
    cC
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @35
    @142
    cB
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    @1
    wcel
    #
    @76
    @72
    wi
    @141
    @153
    @151
    cr
    wcel
    #
    vk
    @29
    wral
    #
    @61
    @88
    @89
    @155
    @61
    @90
    wa
    #
    @154
    vk
    @29
    @156
    @142
    @29
    wcel
    #
    wa
    #
    @148
    @150
    @158
    @36
    @147
    @158
    @106
    @107
    @108
    1re
    @158
    @88
    @107
    @61
    @88
    @89
    @157
    simplrl
    @109
    syl
    #
    @111
    sylancr
    @158
    @144
    @146
    @158
    @13
    @143
    @158
    @106
    @114
    @115
    1re
    @158
    @58
    @114
    @156
    @58
    @157
    @58
    @59
    @0
    @5
    @90
    simpl3l
    adantr
    @116
    syl
    #
    @118
    sylancr
    @156
    @2
    @157
    @143
    cr
    wcel
    @2
    @3
    @4
    @0
    @60
    @90
    simpl21
    cA
    @142
    cN
    fveere
    sylan
    remulcld
    @158
    @12
    @145
    @160
    @156
    @4
    @157
    @145
    cr
    wcel
    @2
    @3
    @4
    @0
    @60
    @90
    simpl23
    cC
    @142
    cN
    fveere
    sylan
    remulcld
    readdcld
    remulcld
    @158
    @35
    @149
    @159
    @156
    @3
    @157
    @149
    cr
    wcel
    @2
    @3
    @4
    @0
    @60
    @90
    simpl22
    cB
    @142
    cN
    fveere
    sylan
    remulcld
    readdcld
    ralrimiva
    anassrs
    @141
    @0
    @153
    @155
    wb
    @0
    @5
    @60
    @88
    @89
    simpll1
    @148
    @150
    vk
    caddc
    cN
    mptelee
    syl
    mpbird
    @153
    @76
    @72
    @69
    @76
    vx
    @152
    @1
    @33
    @152
    wceq
    #
    @68
    @75
    vi
    @29
    @161
    @92
    wa
    #
    @68
    @63
    @63
    wceq
    #
    @75
    wa
    @75
    @162
    @64
    @163
    @67
    @75
    @162
    @34
    @63
    @63
    @161
    @92
    @34
    @10
    @152
    cfv
    @63
    @10
    @33
    @152
    fveq1
    vk
    @10
    @151
    @63
    @29
    @152
    @142
    @10
    wceq
    #
    @148
    @62
    @150
    @38
    caddc
    @164
    @147
    @18
    @36
    cmul
    @164
    @144
    @15
    @146
    @17
    caddc
    @164
    @143
    @14
    @13
    cmul
    @142
    @10
    cA
    fveq2
    oveq2d
    @164
    @145
    @16
    @12
    cmul
    @142
    @10
    cC
    fveq2
    oveq2d
    oveq12d
    oveq2d
    @164
    @149
    @23
    @35
    cmul
    @142
    @10
    cB
    fveq2
    oveq2d
    oveq12d
    @152
    eqid
    @62
    @38
    caddc
    ovex
    fvmpt
    sylan9eq
    #
    eqeq1d
    @162
    @34
    @63
    @66
    @165
    eqeq1d
    anbi12d
    @163
    @75
    @63
    eqid
    biantrur
    syl6bbr
    ralbidva
    rspcev
    ex
    syl
    reximdva
    reximdva
    mpd
    @74
    @70
    vx
    @1
    wrex
    #
    vr
    @31
    wrex
    @71
    @73
    @166
    vr
    @31
    @69
    vq
    vx
    @31
    @1
    rexcom
    rexbii
    @70
    vr
    vx
    @31
    @1
    rexcom
    bitri
    sylib
    @30
    @49
    @70
    vx
    vr
    @1
    @31
    @30
    @48
    @69
    vq
    @31
    @30
    @47
    @68
    wb
    #
    vi
    @29
    wral
    @48
    @69
    wb
    @28
    @167
    vi
    @29
    @19
    @40
    @64
    @27
    @46
    @67
    @19
    @39
    @63
    @34
    @19
    @37
    @62
    @38
    caddc
    @11
    @18
    @36
    cmul
    oveq2
    oveq1d
    eqeq2d
    @27
    @45
    @66
    @34
    @27
    @43
    @65
    @44
    caddc
    @20
    @26
    @42
    cmul
    oveq2
    oveq1d
    eqeq2d
    bi2anan9
    ralimi
    @47
    @68
    vi
    @29
    ralbi
    syl
    rexbidv
    2rexbidv
    syl5ibrcom
    3expia
    rexlimdvv
    3adant3
    @9
    @54
    @19
    vi
    @29
    wral
    #
    vt
    @31
    wrex
    #
    @27
    vi
    @29
    wral
    #
    vs
    @31
    wrex
    #
    wa
    #
    @32
    @9
    @52
    @169
    @53
    @171
    @9
    @6
    @2
    @4
    @52
    @169
    wb
    @0
    @5
    @6
    @7
    simp3l
    @0
    @2
    @3
    @4
    @8
    simp21
    @0
    @2
    @3
    @4
    @8
    simp23
    #
    vt
    cD
    cA
    cC
    vi
    cN
    brbtwn
    syl3anc
    @9
    @7
    @3
    @4
    @53
    @171
    wb
    @0
    @5
    @6
    @7
    simp3r
    @0
    @2
    @3
    @4
    @8
    simp22
    @173
    vs
    cE
    cB
    cC
    vi
    cN
    brbtwn
    syl3anc
    anbi12d
    @32
    @168
    @170
    wa
    #
    vs
    @31
    wrex
    vt
    @31
    wrex
    @172
    @30
    @174
    vt
    vs
    @31
    @31
    @19
    @27
    vi
    @29
    r19.26
    2rexbii
    @168
    @170
    vt
    vs
    @31
    @31
    reeanv
    bitri
    syl6bbr
    @9
    @57
    @50
    vx
    @1
    @9
    @33
    @1
    wcel
    #
    wa
    #
    @57
    @40
    vi
    @29
    wral
    #
    vr
    @31
    wrex
    #
    @46
    vi
    @29
    wral
    #
    vq
    @31
    wrex
    #
    wa
    #
    @50
    @176
    @55
    @178
    @56
    @180
    @176
    @175
    @6
    @3
    @55
    @178
    wb
    @9
    @175
    simpr
    #
    @6
    @7
    @0
    @5
    @175
    simpl3l
    @2
    @3
    @4
    @0
    @8
    @175
    simpl22
    vr
    @33
    cD
    cB
    vi
    cN
    brbtwn
    syl3anc
    @176
    @175
    @7
    @2
    @56
    @180
    wb
    @182
    @6
    @7
    @0
    @5
    @175
    simpl3r
    @2
    @3
    @4
    @0
    @8
    @175
    simpl21
    vq
    @33
    cE
    cA
    vi
    cN
    brbtwn
    syl3anc
    anbi12d
    @50
    @177
    @179
    wa
    #
    vq
    @31
    wrex
    vr
    @31
    wrex
    @181
    @48
    @183
    vr
    vq
    @31
    @31
    @40
    @46
    vi
    @29
    r19.26
    2rexbii
    @177
    @179
    vr
    vq
    @31
    @31
    reeanv
    bitri
    syl6bbr
    rexbidva
    3imtr4d
end
