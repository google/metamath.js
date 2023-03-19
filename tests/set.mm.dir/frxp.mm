include "wfr.mm"
include "wa.mm"
include "cv.mm"
include "cxp.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "cdm.mm"
include "ssn0.mm"
include "xpnz.mm"
include "biimpri.mm"
include "simprd.mm"
include "syl.mm"
include "wceq.mm"
include "dmxp.mm"
include "dmss.mm"
include "sseq2.mm"
include "syl5ib.mm"
include "impcom.mm"
include "syldan.mm"
include "wrel.mm"
include "wb.mm"
include "relxp.mm"
include "relss.mm"
include "mpi.mm"
include "reldm0.mm"
include "necon3bid.mm"
include "biimpa.mm"
include "jca.mm"
include "df-fr.mm"
include "vex.mm"
include "dmex.mm"
include "sseq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "raleq.mm"
include "rexeqbi1dv.mm"
include "imbi12d.mm"
include "spcv.mm"
include "sylbi.mm"
include "syl5.mm"
include "adantr.mm"
include "w3a.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "cima.mm"
include "crn.mm"
include "imassrn.mm"
include "wo.mm"
include "xpeq0.mm"
include "orcs.mm"
include "ss0.mm"
include "syl6bi.mm"
include "rneq.mm"
include "rn0.mm"
include "0ss.mm"
include "eqsstri.mm"
include "syl6eqss.mm"
include "syl6.mm"
include "rnxp.mm"
include "rnss.mm"
include "pm2.61ine.mm"
include "syl5ss.mm"
include "wex.mm"
include "eldm.mm"
include "elimasn.mm"
include "df-br.mm"
include "bitr4i.mm"
include "ne0i.mm"
include "sylbir.mm"
include "exlimiv.mm"
include "imaex.mm"
include "syl2ani.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "1stdm.mm"
include "breq1.mm"
include "notbid.mm"
include "rspccv.mm"
include "expd.mm"
include "elrel.mm"
include "ex.mm"
include "weq.mm"
include "syl5bir.mm"
include "adantl.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "imbi1d.mm"
include "syl5ibr.mm"
include "com3l.mm"
include "eleq1.mm"
include "op1std.mm"
include "eqeq1d.mm"
include "op2ndd.mm"
include "breq1d.mm"
include "exlimivv.mm"
include "mpdd.mm"
include "adantlr.mm"
include "jcad.mm"
include "ralrimiv.mm"
include "sylan.mm"
include "olc.mm"
include "ralimi.mm"
include "ianor.mm"
include "opex.mm"
include "anbi1d.mm"
include "fveq2.mm"
include "orbi12d.mm"
include "anbi2d.mm"
include "breq2d.mm"
include "eqeq2d.mm"
include "brab.mm"
include "xchnxbir.mm"
include "ioran.mm"
include "pm4.62.mm"
include "anbi2i.mm"
include "bitri.mm"
include "orbi2i.mm"
include "ralbii.mm"
include "syl6ibr.mm"
include "reximdv.mm"
include "com23.mm"
include "sylcom.mm"
include "impl.mm"
include "expimpd.mm"
include "3adant3.mm"
include "cres.mm"
include "resss.mm"
include "df-rex.mm"
include "eqid.mm"
include "eqeq1.mm"
include "breq2.mm"
include "ralbidv.mm"
include "spcev.mm"
include "mpan.mm"
include "sylanb.mm"
include "eximi.mm"
include "excom.mm"
include "sylib.mm"
include "elsnres.mm"
include "anbi1i.mm"
include "19.41v.mm"
include "anass.mm"
include "exbii.mm"
include "3bitr2i.mm"
include "sylibr.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "rexlimdv.mm"
include "3expib.mm"
include "alrimiv.mm"

theorem frxp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vs: setvar s
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let vd: setvar d
  let vt: setvar t
  let vu: setvar u
  assume frxp.1: |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A s
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint a b
  disjoint a c
  disjoint a s
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b s
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c s
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint B a
  disjoint B b
  disjoint B d
  disjoint B s
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint a d
  disjoint b d
  disjoint d s
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R s
  disjoint R v
  disjoint R w
  disjoint S a
  disjoint S b
  disjoint S d
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint a t
  disjoint a u
  disjoint b t
  disjoint b u
  disjoint d t
  disjoint d u
  disjoint s t
  disjoint s u
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint T a
  disjoint T b
  disjoint T s
  disjoint T w
  disjoint T z
  assert |- ( ( R Fr A /\ S Fr B ) -> T Fr ( A X. B ) )

  proof
    cA
    cR
    wfr
    #
    cB
    cS
    wfr
    #
    wa
    #
    vs
    cv
    #
    cA
    cB
    cxp
    #
    wss
    #
    @3
    c0
    wne
    #
    wa
    #
    vw
    cv
    #
    vz
    cv
    #
    cT
    wbr
    #
    wn
    #
    vw
    @3
    wral
    #
    vz
    @3
    wrex
    #
    wi
    #
    vs
    wal
    @4
    cT
    wfr
    @2
    @14
    vs
    @2
    @7
    vc
    cv
    #
    va
    cv
    #
    cR
    wbr
    #
    wn
    #
    vc
    @3
    cdm
    #
    wral
    #
    va
    @19
    wrex
    #
    @13
    @0
    @7
    @21
    wi
    @1
    @7
    @19
    cA
    wss
    #
    @19
    c0
    wne
    #
    wa
    #
    @0
    @21
    @7
    @22
    @23
    @5
    @6
    cB
    c0
    wne
    #
    @22
    @7
    @4
    c0
    wne
    #
    @25
    @3
    @4
    ssn0
    @26
    cA
    c0
    wne
    #
    @25
    @27
    @25
    wa
    @26
    cA
    cB
    xpnz
    biimpri
    simprd
    syl
    @25
    @5
    @22
    @25
    @4
    cdm
    #
    cA
    wceq
    #
    @5
    @22
    wi
    cA
    cB
    dmxp
    @5
    @19
    @28
    wss
    @29
    @22
    @3
    @4
    dmss
    @28
    cA
    @19
    sseq2
    syl5ib
    syl
    impcom
    syldan
    @5
    @6
    @23
    @5
    @3
    c0
    @19
    c0
    @5
    @3
    wrel
    #
    @3
    c0
    wceq
    #
    @19
    c0
    wceq
    wb
    @5
    @4
    wrel
    @30
    cA
    cB
    relxp
    @3
    @4
    relss
    mpi
    #
    @3
    reldm0
    syl
    necon3bid
    biimpa
    jca
    @0
    vv
    cv
    #
    cA
    wss
    #
    @33
    c0
    wne
    #
    wa
    #
    @18
    vc
    @33
    wral
    #
    va
    @33
    wrex
    #
    wi
    #
    vv
    wal
    @24
    @21
    wi
    #
    vv
    va
    vc
    cA
    cR
    df-fr
    @39
    @40
    vv
    @19
    @3
    vs
    vex
    #
    dmex
    @33
    @19
    wceq
    #
    @36
    @24
    @38
    @21
    @42
    @34
    @22
    @35
    @23
    @33
    @19
    cA
    sseq1
    @33
    @19
    c0
    neeq1
    anbi12d
    @37
    @20
    va
    @33
    @19
    @18
    vc
    @33
    @19
    raleq
    rexeqbi1dv
    imbi12d
    spcv
    sylbi
    syl5
    adantr
    @1
    @7
    @21
    @13
    wi
    #
    wi
    @0
    @1
    @5
    @6
    @43
    @1
    @5
    @6
    w3a
    #
    @20
    @13
    va
    @19
    @44
    @16
    @19
    wcel
    #
    @20
    @13
    @44
    @45
    @20
    wa
    #
    @8
    @16
    vb
    cv
    #
    cop
    #
    cT
    wbr
    #
    wn
    #
    vw
    @3
    wral
    #
    vb
    @3
    @16
    csn
    #
    cima
    #
    wrex
    #
    @13
    @1
    @5
    @46
    @54
    wi
    @6
    @1
    @5
    wa
    @45
    @20
    @54
    @1
    @5
    @45
    @20
    @54
    wi
    #
    @1
    @5
    @45
    wa
    vd
    cv
    #
    @47
    cS
    wbr
    #
    wn
    #
    vd
    @53
    wral
    #
    vb
    @53
    wrex
    #
    @55
    @5
    @1
    @53
    cB
    wss
    #
    @53
    c0
    wne
    #
    @60
    @45
    @5
    @53
    @3
    crn
    #
    cB
    @3
    @52
    imassrn
    @5
    @63
    cB
    wss
    #
    wi
    #
    cA
    c0
    cA
    c0
    wceq
    #
    @5
    @31
    @64
    @66
    @4
    c0
    wceq
    #
    @5
    @31
    wi
    @66
    cB
    c0
    wceq
    #
    @67
    @67
    @66
    @68
    wo
    cA
    cB
    xpeq0
    biimpri
    orcs
    @67
    @5
    @3
    c0
    wss
    @31
    @4
    c0
    @3
    sseq2
    @3
    ss0
    syl6bi
    syl
    @31
    @63
    c0
    crn
    #
    cB
    @3
    c0
    rneq
    @69
    c0
    cB
    rn0
    cB
    0ss
    eqsstri
    syl6eqss
    syl6
    @27
    @4
    crn
    #
    cB
    wceq
    #
    @65
    cA
    cB
    rnxp
    @5
    @63
    @70
    wss
    @71
    @64
    @3
    @4
    rnss
    @70
    cB
    @63
    sseq2
    syl5ib
    syl
    pm2.61ine
    syl5ss
    @45
    @16
    @47
    @3
    wbr
    #
    vb
    wex
    @62
    vb
    @16
    @3
    va
    vex
    #
    eldm
    @72
    @62
    vb
    @72
    @47
    @53
    wcel
    #
    @62
    @74
    @48
    @3
    wcel
    #
    @72
    @3
    @16
    @47
    @73
    vb
    vex
    #
    elimasn
    #
    @16
    @47
    @3
    df-br
    bitr4i
    @53
    @47
    ne0i
    sylbir
    exlimiv
    sylbi
    @1
    @33
    cB
    wss
    #
    @35
    wa
    #
    @58
    vd
    @33
    wral
    #
    vb
    @33
    wrex
    #
    wi
    #
    vv
    wal
    @61
    @62
    wa
    #
    @60
    wi
    #
    vv
    vb
    vd
    cB
    cS
    df-fr
    @82
    @84
    vv
    @53
    @3
    @52
    @41
    imaex
    @33
    @53
    wceq
    #
    @79
    @83
    @81
    @60
    @85
    @78
    @61
    @35
    @62
    @33
    @53
    cB
    sseq1
    @33
    @53
    c0
    neeq1
    anbi12d
    @80
    @59
    vb
    @33
    @53
    @58
    vd
    @33
    @53
    raleq
    rexeqbi1dv
    imbi12d
    spcv
    sylbi
    syl2ani
    @5
    @60
    @55
    wi
    @45
    @5
    @20
    @60
    @54
    @5
    @20
    @60
    @54
    wi
    @5
    @20
    wa
    #
    @59
    @51
    vb
    @53
    @86
    @59
    @8
    @4
    wcel
    #
    @48
    @4
    wcel
    #
    wa
    #
    wn
    #
    @8
    c1st
    cfv
    #
    @16
    cR
    wbr
    #
    wn
    #
    @91
    @16
    wceq
    #
    @8
    c2nd
    cfv
    #
    @47
    cS
    wbr
    #
    wn
    #
    wi
    #
    wa
    #
    wo
    #
    vw
    @3
    wral
    #
    @51
    @86
    @59
    @99
    vw
    @3
    wral
    #
    @101
    @5
    @30
    @20
    @59
    @102
    wi
    @32
    @30
    @20
    wa
    #
    @59
    @102
    @103
    @59
    wa
    #
    @99
    vw
    @3
    @104
    @8
    @3
    wcel
    #
    @93
    @98
    @103
    @105
    @93
    wi
    #
    @59
    @20
    @30
    @106
    @20
    @30
    @105
    @93
    @30
    @105
    wa
    @91
    @19
    wcel
    @20
    @93
    @8
    @3
    1stdm
    @18
    @93
    vc
    @91
    @19
    @15
    @91
    wceq
    @17
    @92
    @15
    @91
    @16
    cR
    breq1
    notbid
    rspccv
    syl5
    expd
    impcom
    adantr
    @30
    @59
    @105
    @98
    wi
    #
    @20
    @30
    @59
    wa
    #
    @105
    @8
    vt
    cv
    #
    vu
    cv
    #
    cop
    #
    wceq
    #
    vu
    wex
    vt
    wex
    #
    @98
    @30
    @105
    @113
    wi
    @59
    @30
    @105
    @113
    vt
    vu
    @8
    @3
    elrel
    ex
    adantr
    @113
    @108
    @105
    @98
    @112
    @108
    @107
    wi
    vt
    vu
    @108
    @107
    @112
    @111
    @3
    wcel
    #
    vt
    va
    weq
    #
    @110
    @47
    cS
    wbr
    #
    wn
    #
    wi
    #
    wi
    @115
    @108
    @114
    @117
    @108
    @114
    @117
    wi
    @115
    @16
    @110
    cop
    #
    @3
    wcel
    #
    @117
    wi
    #
    @59
    @121
    @30
    @120
    @110
    @53
    wcel
    @59
    @117
    @3
    @16
    @110
    @73
    vu
    vex
    #
    elimasn
    @58
    @117
    vd
    @110
    @53
    vd
    vu
    weq
    @57
    @116
    @56
    @110
    @47
    cS
    breq1
    notbid
    rspccv
    syl5bir
    adantl
    @115
    @114
    @120
    @117
    @115
    @111
    @119
    @3
    @109
    @16
    @110
    opeq1
    eleq1d
    imbi1d
    syl5ibr
    com3l
    @112
    @105
    @114
    @98
    @118
    @8
    @111
    @3
    eleq1
    @112
    @94
    @115
    @97
    @117
    @112
    @91
    @109
    @16
    @109
    @110
    @8
    vt
    vex
    #
    @122
    op1std
    eqeq1d
    @112
    @96
    @116
    @112
    @95
    @110
    @47
    cS
    @109
    @110
    @8
    @123
    @122
    op2ndd
    breq1d
    notbid
    imbi12d
    imbi12d
    syl5ibr
    exlimivv
    com3l
    mpdd
    adantlr
    jcad
    ralrimiv
    ex
    sylan
    @99
    @100
    vw
    @3
    @99
    @90
    olc
    ralimi
    syl6
    @50
    @100
    vw
    @3
    @50
    @90
    @92
    @94
    @96
    wa
    #
    wo
    #
    wn
    #
    wo
    #
    @100
    @89
    @125
    wa
    #
    @127
    @49
    @89
    @125
    ianor
    vx
    cv
    #
    @4
    wcel
    #
    vy
    cv
    #
    @4
    wcel
    #
    wa
    #
    @129
    c1st
    cfv
    #
    @131
    c1st
    cfv
    #
    cR
    wbr
    #
    @134
    @135
    wceq
    #
    @129
    c2nd
    cfv
    #
    @131
    c2nd
    cfv
    #
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    @87
    @132
    wa
    #
    @91
    @135
    cR
    wbr
    #
    @91
    @135
    wceq
    #
    @95
    @139
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    @128
    vx
    vy
    @8
    @48
    cT
    vw
    vex
    @16
    @47
    opex
    #
    vx
    vw
    weq
    #
    @133
    @143
    @142
    @148
    @150
    @130
    @87
    @132
    @129
    @8
    @4
    eleq1
    anbi1d
    @150
    @136
    @144
    @141
    @147
    @150
    @134
    @91
    @135
    cR
    @129
    @8
    c1st
    fveq2
    #
    breq1d
    @150
    @137
    @145
    @140
    @146
    @150
    @134
    @91
    @135
    @151
    eqeq1d
    @150
    @138
    @95
    @139
    cS
    @129
    @8
    c2nd
    fveq2
    breq1d
    anbi12d
    orbi12d
    anbi12d
    @131
    @48
    wceq
    #
    @143
    @89
    @148
    @125
    @152
    @132
    @88
    @87
    @131
    @48
    @4
    eleq1
    anbi2d
    @152
    @144
    @92
    @147
    @124
    @152
    @135
    @16
    @91
    cR
    @16
    @47
    @131
    @73
    @76
    op1std
    #
    breq2d
    @152
    @145
    @94
    @146
    @96
    @152
    @135
    @16
    @91
    @153
    eqeq2d
    @152
    @139
    @47
    @95
    cS
    @16
    @47
    @131
    @73
    @76
    op2ndd
    breq2d
    anbi12d
    orbi12d
    anbi12d
    frxp.1
    brab
    xchnxbir
    @126
    @99
    @90
    @126
    @93
    @124
    wn
    #
    wa
    @99
    @92
    @124
    ioran
    @154
    @98
    @93
    @154
    @94
    wn
    @97
    wo
    @98
    @94
    @96
    ianor
    @94
    @96
    pm4.62
    bitr4i
    anbi2i
    bitri
    orbi2i
    bitri
    ralbii
    syl6ibr
    reximdv
    ex
    com23
    adantr
    sylcom
    impl
    expimpd
    3adant3
    @3
    @52
    cres
    #
    @3
    wss
    @54
    @12
    vz
    @155
    wrex
    #
    @13
    @3
    @52
    resss
    @54
    @9
    @48
    wceq
    #
    @75
    @12
    wa
    #
    wa
    #
    vb
    wex
    #
    vz
    wex
    #
    @156
    @54
    @159
    vz
    wex
    #
    vb
    wex
    #
    @161
    @54
    @74
    @51
    wa
    #
    vb
    wex
    @163
    @51
    vb
    @53
    df-rex
    @164
    @162
    vb
    @74
    @75
    @51
    @162
    @77
    @48
    @48
    wceq
    #
    @75
    @51
    wa
    #
    @162
    @48
    eqid
    @159
    @165
    @166
    wa
    vz
    @48
    @149
    @157
    @157
    @165
    @158
    @166
    @9
    @48
    @48
    eqeq1
    @157
    @12
    @51
    @75
    @157
    @11
    @50
    vw
    @3
    @157
    @10
    @49
    @9
    @48
    @8
    cT
    breq2
    notbid
    ralbidv
    anbi2d
    anbi12d
    spcev
    mpan
    sylanb
    eximi
    sylbi
    @159
    vb
    vz
    excom
    sylib
    @156
    @9
    @155
    wcel
    #
    @12
    wa
    #
    vz
    wex
    @161
    @12
    vz
    @155
    df-rex
    @168
    @160
    vz
    @168
    @157
    @75
    wa
    #
    vb
    wex
    #
    @12
    wa
    @169
    @12
    wa
    #
    vb
    wex
    @160
    @167
    @170
    @12
    vb
    @9
    @3
    @16
    @73
    elsnres
    anbi1i
    @169
    @12
    vb
    19.41v
    @171
    @159
    vb
    @157
    @75
    @12
    anass
    exbii
    3bitr2i
    exbii
    bitri
    sylibr
    @12
    vz
    @155
    @3
    ssrexv
    mpsyl
    syl6
    expd
    rexlimdv
    3expib
    adantl
    mpdd
    alrimiv
    vs
    vz
    vw
    @4
    cT
    df-fr
    sylibr
end
