include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "ceq.mm"
include "wbr.mm"
include "cnq.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cop.mm"
include "wceq.mm"
include "elxp2.mm"
include "wel.mm"
include "con0.mm"
include "csuc.mm"
include "pion.mm"
include "suceloni.mm"
include "syl.mm"
include "vex.mm"
include "sucid.mm"
include "eleq2.mm"
include "rspcev.mm"
include "sylancl.mm"
include "adantl.mm"
include "elequ2.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "opeq1.mm"
include "breq2d.mm"
include "rexbidv.mm"
include "imbi2d.mm"
include "elequ1.mm"
include "opeq2.mm"
include "imbi12d.mm"
include "cbvral2v.mm"
include "ralbii.mm"
include "c2nd.mm"
include "cfv.mm"
include "clti.mm"
include "wn.mm"
include "rexnal.mm"
include "pm4.63.mm"
include "wb.mm"
include "xp2nd.mm"
include "ltpiord.mm"
include "ancoms.mm"
include "sylan2.mm"
include "adantll.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "syl5bbr.mm"
include "w3a.mm"
include "c1st.mm"
include "xp1st.mm"
include "rspccv.mm"
include "ralbidv.mm"
include "eleq1.mm"
include "syl6.mm"
include "imp.mm"
include "syl5.mm"
include "mpdi.mm"
include "3imp.mm"
include "1st2nd2.mm"
include "3ad2ant2.mm"
include "mpbird.mm"
include "wer.mm"
include "enqer.mm"
include "a1i.mm"
include "simpr.mm"
include "simpl.mm"
include "ertr4d.mm"
include "ex.mm"
include "reximdv.mm"
include "syl5com.mm"
include "3expia.mm"
include "com23.mm"
include "impd.mm"
include "rexlimdva.mm"
include "com3r.mm"
include "syl6bi.mm"
include "com13.mm"
include "cmi.mm"
include "co.mm"
include "mulcompi.mm"
include "enqbreq.mm"
include "anidms.mm"
include "mpbiri.mm"
include "opelxpi.mm"
include "breq1.mm"
include "op2ndd.mm"
include "notbid.mm"
include "df-nq.mm"
include "elrab2.mm"
include "simplbi2.mm"
include "expcom.mm"
include "sylsyld.mm"
include "com12.mm"
include "a1dd.mm"
include "pm2.61d2.mm"
include "ralrimivv.mm"
include "sylbir.mm"
include "tfis2.mm"
include "rsp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "anbi12d.mm"
include "elpqn.mm"
include "fveq2.mm"
include "simprbi.mm"
include "breq1d.mm"
include "rspcva.mm"
include "syl2anr.mm"
include "wo.mm"
include "id.mm"
include "ersym.mm"
include "rabeq2i.mm"
include "syl2an.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "wor.mm"
include "ltsopi.mm"
include "sotric.mm"
include "mpan.mm"
include "notnotb.mm"
include "syl6bbr.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ord.mm"
include "mt3d.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "breqan12d.mm"
include "jca.mm"
include "bitrd.mm"
include "biimpa.mm"
include "eqtrd.mm"
include "mulcanpi.mm"
include "opeq12d.mm"
include "3eqtr4d.mm"
include "rgen2a.mm"
include "vtoclg.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem nqereu
  let vx: setvar x
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vz: setvar z

  disjoint A x
  disjoint A a
  disjoint A b
  disjoint A y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint a c
  disjoint a d
  disjoint a m
  disjoint a z
  disjoint b c
  disjoint b d
  disjoint b m
  disjoint b z
  disjoint c d
  disjoint c m
  disjoint c x
  disjoint c z
  disjoint d m
  disjoint d x
  disjoint d z
  disjoint m x
  disjoint m z
  disjoint x z
  disjoint m y
  disjoint y z
  assert |- ( A e. ( N. X. N. ) -> E! x e. Q. x ~Q A )

  proof
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    vx
    cv
    #
    cA
    ceq
    wbr
    #
    vx
    cnq
    wrex
    #
    @3
    vy
    cv
    #
    cA
    ceq
    wbr
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cnq
    wral
    vx
    cnq
    wral
    #
    @3
    vx
    cnq
    wreu
    @1
    cA
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    vb
    cnpi
    wrex
    va
    cnpi
    wrex
    @4
    va
    vb
    cA
    cnpi
    cnpi
    elxp2
    @14
    @4
    va
    vb
    cnpi
    cnpi
    @11
    cnpi
    wcel
    #
    @12
    cnpi
    wcel
    #
    wa
    #
    @4
    @14
    @2
    @13
    ceq
    wbr
    #
    vx
    cnq
    wrex
    #
    @17
    vb
    vy
    wel
    #
    vy
    con0
    wrex
    #
    @19
    @16
    @21
    @15
    @16
    @12
    csuc
    #
    con0
    wcel
    #
    @12
    @22
    wcel
    #
    @21
    @16
    @12
    con0
    wcel
    @23
    @12
    pion
    @12
    suceloni
    syl
    @12
    vb
    vex
    #
    sucid
    @20
    @24
    vy
    @22
    con0
    @5
    @22
    @12
    eleq2
    rspcev
    sylancl
    adantl
    @17
    @20
    @19
    vy
    con0
    @5
    con0
    wcel
    #
    @17
    @20
    @19
    wi
    #
    @26
    @15
    @16
    @27
    @26
    @15
    @27
    vb
    cnpi
    wral
    #
    @16
    @27
    wi
    @26
    @28
    va
    cnpi
    wral
    #
    @15
    @28
    wi
    @29
    vb
    vm
    wel
    #
    @19
    wi
    #
    vb
    cnpi
    wral
    va
    cnpi
    wral
    #
    vy
    vm
    vy
    vm
    weq
    #
    @27
    @31
    va
    vb
    cnpi
    cnpi
    @33
    @20
    @30
    @19
    vy
    vm
    vb
    elequ2
    imbi1d
    2ralbidv
    @32
    vm
    @5
    wral
    #
    @29
    wi
    @26
    @34
    vd
    vm
    wel
    #
    @2
    vc
    cv
    #
    vd
    cv
    #
    cop
    #
    ceq
    wbr
    #
    vx
    cnq
    wrex
    #
    wi
    #
    vd
    cnpi
    wral
    vc
    cnpi
    wral
    #
    vm
    @5
    wral
    #
    @29
    @42
    @32
    vm
    @5
    @41
    @31
    @35
    @2
    @11
    @37
    cop
    #
    ceq
    wbr
    #
    vx
    cnq
    wrex
    #
    wi
    vc
    vd
    va
    vb
    cnpi
    cnpi
    vc
    va
    weq
    #
    @40
    @46
    @35
    @47
    @39
    @45
    vx
    cnq
    @47
    @38
    @44
    @2
    ceq
    @36
    @11
    @37
    opeq1
    breq2d
    rexbidv
    imbi2d
    vd
    vb
    weq
    #
    @35
    @30
    @46
    @19
    vd
    vb
    vm
    elequ1
    @48
    @45
    @18
    vx
    cnq
    @48
    @44
    @13
    @2
    ceq
    @37
    @12
    @11
    opeq2
    breq2d
    rexbidv
    imbi12d
    cbvral2v
    ralbii
    @43
    @27
    va
    vb
    cnpi
    cnpi
    @43
    @13
    vz
    cv
    #
    ceq
    wbr
    #
    @49
    c2nd
    cfv
    #
    @12
    clti
    wbr
    #
    wn
    #
    wi
    #
    vz
    @0
    wral
    #
    @17
    @27
    wi
    @17
    @55
    wn
    #
    @43
    @27
    @17
    @56
    @50
    @51
    @12
    wcel
    #
    wa
    #
    vz
    @0
    wrex
    #
    @43
    @27
    wi
    @56
    @54
    wn
    #
    vz
    @0
    wrex
    @17
    @59
    @54
    vz
    @0
    rexnal
    @17
    @60
    @58
    vz
    @0
    @60
    @50
    @52
    wa
    @17
    @49
    @0
    wcel
    #
    wa
    #
    @58
    @50
    @52
    pm4.63
    @62
    @52
    @57
    @50
    @16
    @61
    @52
    @57
    wb
    #
    @15
    @61
    @16
    @51
    cnpi
    wcel
    #
    @63
    @49
    cnpi
    cnpi
    xp2nd
    #
    @64
    @16
    @63
    @51
    @12
    ltpiord
    ancoms
    sylan2
    adantll
    anbi2d
    syl5bb
    rexbidva
    syl5bbr
    @43
    @20
    @59
    @19
    @43
    @20
    @59
    @19
    wi
    @43
    @20
    wa
    #
    @58
    @19
    vz
    @0
    @66
    @61
    wa
    #
    @50
    @57
    @19
    @67
    @57
    @50
    @19
    @66
    @61
    @57
    @50
    @19
    wi
    @66
    @61
    @57
    w3a
    #
    @2
    @49
    ceq
    wbr
    #
    vx
    cnq
    wrex
    #
    @50
    @19
    @68
    @70
    @2
    @49
    c1st
    cfv
    #
    @51
    cop
    #
    ceq
    wbr
    #
    vx
    cnq
    wrex
    #
    @66
    @61
    @57
    @74
    @66
    @61
    @64
    @57
    @74
    wi
    #
    @65
    @61
    @71
    cnpi
    wcel
    #
    @66
    @64
    @75
    wi
    #
    @49
    cnpi
    cnpi
    xp1st
    @43
    @20
    @76
    @77
    wi
    #
    @43
    @20
    vd
    vb
    wel
    #
    @40
    wi
    #
    vd
    cnpi
    wral
    #
    vc
    cnpi
    wral
    #
    @78
    @42
    @82
    vm
    @12
    @5
    vm
    vb
    weq
    #
    @41
    @80
    vc
    vd
    cnpi
    cnpi
    @83
    @35
    @79
    @40
    vm
    vb
    vd
    elequ2
    imbi1d
    2ralbidv
    rspccv
    @82
    @76
    @79
    @2
    @71
    @37
    cop
    #
    ceq
    wbr
    #
    vx
    cnq
    wrex
    #
    wi
    #
    vd
    cnpi
    wral
    #
    @77
    @81
    @88
    vc
    @71
    cnpi
    @36
    @71
    wceq
    #
    @80
    @87
    vd
    cnpi
    @89
    @40
    @86
    @79
    @89
    @39
    @85
    vx
    cnq
    @89
    @38
    @84
    @2
    ceq
    @36
    @71
    @37
    opeq1
    breq2d
    rexbidv
    imbi2d
    ralbidv
    rspccv
    @87
    @75
    vd
    @51
    cnpi
    @37
    @51
    wceq
    #
    @79
    @57
    @86
    @74
    @37
    @51
    @12
    eleq1
    @90
    @85
    @73
    vx
    cnq
    @90
    @84
    @72
    @2
    ceq
    @37
    @51
    @71
    opeq2
    breq2d
    rexbidv
    imbi12d
    rspccv
    syl6
    syl6
    imp
    syl5
    mpdi
    3imp
    @61
    @66
    @70
    @74
    wb
    @57
    @61
    @69
    @73
    vx
    cnq
    @61
    @49
    @72
    @2
    ceq
    @49
    cnpi
    cnpi
    1st2nd2
    breq2d
    rexbidv
    3ad2ant2
    mpbird
    @50
    @69
    @18
    vx
    cnq
    @50
    @69
    @18
    @50
    @69
    wa
    #
    @2
    @49
    @13
    ceq
    @0
    @0
    ceq
    wer
    #
    @91
    enqer
    a1i
    @50
    @69
    simpr
    @50
    @69
    simpl
    ertr4d
    ex
    reximdv
    syl5com
    3expia
    com23
    impd
    rexlimdva
    ex
    com3r
    syl6bi
    com13
    @55
    @17
    @19
    @20
    @17
    @55
    @19
    @17
    @13
    @13
    ceq
    wbr
    #
    @55
    @13
    cnq
    wcel
    #
    @19
    @17
    @93
    @11
    @12
    cmi
    co
    @12
    @11
    cmi
    co
    wceq
    #
    @11
    @12
    mulcompi
    @17
    @93
    @95
    wb
    @11
    @12
    @11
    @12
    enqbreq
    anidms
    mpbiri
    @17
    @13
    @0
    wcel
    #
    @55
    @94
    wi
    @11
    @12
    cnpi
    cnpi
    opelxpi
    @94
    @96
    @55
    @5
    @49
    ceq
    wbr
    #
    @51
    @5
    c2nd
    cfv
    #
    clti
    wbr
    #
    wn
    #
    wi
    #
    vz
    @0
    wral
    #
    @55
    vy
    @13
    @0
    cnq
    @5
    @13
    wceq
    #
    @101
    @54
    vz
    @0
    @103
    @97
    @50
    @100
    @53
    @5
    @13
    @49
    ceq
    breq1
    @103
    @99
    @52
    @103
    @98
    @12
    @51
    clti
    @11
    @12
    @5
    va
    vex
    @25
    op2ndd
    breq2d
    notbid
    imbi12d
    ralbidv
    vy
    vz
    df-nq
    #
    elrab2
    simplbi2
    syl
    @94
    @93
    @19
    @18
    @93
    vx
    @13
    cnq
    @2
    @13
    @13
    ceq
    breq1
    rspcev
    expcom
    sylsyld
    com12
    a1dd
    pm2.61d2
    ralrimivv
    sylbir
    a1i
    tfis2
    @28
    va
    cnpi
    rsp
    syl
    @27
    vb
    cnpi
    rsp
    syl6
    impd
    com12
    rexlimdv
    mpd
    @14
    @3
    @18
    vx
    cnq
    cA
    @13
    @2
    ceq
    breq2
    rexbidv
    syl5ibrcom
    rexlimivv
    sylbi
    @2
    @11
    ceq
    wbr
    #
    @5
    @11
    ceq
    wbr
    #
    wa
    #
    @8
    wi
    #
    vy
    cnq
    wral
    vx
    cnq
    wral
    @10
    va
    cA
    @0
    @11
    cA
    wceq
    #
    @108
    @9
    vx
    vy
    cnq
    cnq
    @109
    @107
    @7
    @8
    @109
    @105
    @3
    @106
    @6
    @11
    cA
    @2
    ceq
    breq2
    @11
    cA
    @5
    ceq
    breq2
    anbi12d
    imbi1d
    2ralbidv
    @108
    vx
    vy
    cnq
    @107
    @2
    @5
    ceq
    wbr
    #
    @2
    cnq
    wcel
    #
    @5
    cnq
    wcel
    #
    wa
    #
    @8
    @107
    @2
    @11
    @5
    ceq
    @0
    @92
    @107
    enqer
    a1i
    @105
    @106
    simpl
    @105
    @106
    simpr
    ertr4d
    @113
    @110
    @8
    @113
    @110
    wa
    #
    @2
    c1st
    cfv
    #
    @2
    c2nd
    cfv
    #
    cop
    #
    @5
    c1st
    cfv
    #
    @98
    cop
    #
    @2
    @5
    @114
    @115
    @118
    @116
    @98
    @114
    @116
    @115
    cmi
    co
    #
    @116
    @118
    cmi
    co
    #
    wceq
    #
    @115
    @118
    wceq
    #
    @114
    @120
    @115
    @98
    cmi
    co
    #
    @121
    @114
    @120
    @115
    @116
    cmi
    co
    @124
    @116
    @115
    mulcompi
    @114
    @116
    @98
    @115
    cmi
    @114
    @116
    @98
    wceq
    #
    @98
    @116
    clti
    wbr
    #
    @113
    @110
    @126
    wn
    #
    @112
    @5
    @0
    wcel
    #
    @69
    @51
    @116
    clti
    wbr
    #
    wn
    #
    wi
    #
    vz
    @0
    wral
    #
    @110
    @127
    wi
    #
    @111
    @5
    elpqn
    #
    @111
    @2
    @0
    wcel
    #
    @132
    @102
    @132
    vy
    @2
    @0
    cnq
    vy
    vx
    weq
    #
    @101
    @131
    vz
    @0
    @136
    @97
    @69
    @100
    @130
    @5
    @2
    @49
    ceq
    breq1
    @136
    @99
    @129
    @136
    @98
    @116
    @51
    clti
    @5
    @2
    c2nd
    fveq2
    breq2d
    notbid
    imbi12d
    ralbidv
    @104
    elrab2
    simprbi
    @131
    @133
    vz
    @5
    @0
    vz
    vy
    weq
    #
    @69
    @110
    @130
    @127
    @49
    @5
    @2
    ceq
    breq2
    @137
    @129
    @126
    @137
    @51
    @98
    @116
    clti
    @49
    @5
    c2nd
    fveq2
    breq1d
    notbid
    imbi12d
    rspcva
    syl2anr
    imp
    @114
    @125
    @126
    @114
    @116
    @98
    clti
    wbr
    #
    wn
    #
    @125
    @126
    wo
    #
    @113
    @110
    @139
    @110
    @5
    @2
    ceq
    wbr
    #
    @113
    @139
    @110
    @2
    @5
    ceq
    @0
    @92
    @110
    enqer
    a1i
    @110
    id
    ersym
    @111
    @135
    @102
    @141
    @139
    wi
    #
    @112
    @2
    elpqn
    #
    @112
    @128
    @102
    @102
    vy
    cnq
    @0
    @104
    rabeq2i
    simprbi
    @101
    @142
    vz
    @2
    @0
    vz
    vx
    weq
    #
    @97
    @141
    @100
    @139
    @49
    @2
    @5
    ceq
    breq2
    @144
    @99
    @138
    @144
    @51
    @116
    @98
    clti
    @49
    @2
    c2nd
    fveq2
    breq1d
    notbid
    imbi12d
    rspcva
    syl2an
    syl5
    imp
    @114
    @116
    cnpi
    wcel
    #
    @98
    cnpi
    wcel
    #
    @139
    @140
    wb
    @111
    @145
    @112
    @110
    @111
    @135
    @145
    @143
    @2
    cnpi
    cnpi
    xp2nd
    #
    syl
    ad2antrr
    @112
    @146
    @111
    @110
    @112
    @128
    @146
    @134
    @5
    cnpi
    cnpi
    xp2nd
    #
    syl
    ad2antlr
    @145
    @146
    wa
    #
    @139
    @140
    wn
    #
    wn
    @140
    @149
    @138
    @150
    cnpi
    clti
    wor
    @149
    @138
    @150
    wb
    ltsopi
    cnpi
    @116
    @98
    clti
    sotric
    mpan
    notbid
    @140
    notnotb
    syl6bbr
    syl2anc
    mpbid
    ord
    mt3d
    #
    oveq2d
    syl5eq
    @113
    @110
    @124
    @121
    wceq
    #
    @111
    @135
    @128
    @110
    @152
    wb
    @112
    @143
    @134
    @135
    @128
    wa
    @110
    @117
    @119
    ceq
    wbr
    #
    @152
    @135
    @128
    @2
    @117
    @5
    @119
    ceq
    @2
    cnpi
    cnpi
    1st2nd2
    #
    @5
    cnpi
    cnpi
    1st2nd2
    #
    breqan12d
    @135
    @115
    cnpi
    wcel
    #
    @145
    wa
    @118
    cnpi
    wcel
    #
    @146
    wa
    @153
    @152
    wb
    @128
    @135
    @156
    @145
    @2
    cnpi
    cnpi
    xp1st
    #
    @147
    jca
    @128
    @157
    @146
    @5
    cnpi
    cnpi
    xp1st
    @148
    jca
    @115
    @116
    @118
    @98
    enqbreq
    syl2an
    bitrd
    syl2an
    biimpa
    eqtrd
    @114
    @135
    @122
    @123
    wb
    #
    @111
    @135
    @112
    @110
    @143
    ad2antrr
    #
    @135
    @145
    @156
    @159
    @147
    @158
    @116
    @115
    @118
    mulcanpi
    syl2anc
    syl
    mpbid
    @151
    opeq12d
    @114
    @135
    @2
    @117
    wceq
    @160
    @154
    syl
    @114
    @128
    @5
    @119
    wceq
    @112
    @128
    @111
    @110
    @134
    ad2antlr
    @155
    syl
    3eqtr4d
    ex
    syl5
    rgen2a
    vtoclg
    @3
    @6
    vx
    vy
    cnq
    @2
    @5
    cA
    ceq
    breq1
    reu4
    sylanbrc
end
