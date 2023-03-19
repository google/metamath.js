include "ccat.mm"
include "wcel.mm"
include "ccid.mm"
include "cfv.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "cmpt2.mm"
include "chom.mm"
include "co.mm"
include "w3a.mm"
include "cco.mm"
include "cvv.mm"
include "cbs.mm"
include "xpcbas.mm"
include "a1i.mm"
include "eqidd.mm"
include "cxpc.mm"
include "ovex.mm"
include "eqeltri.mm"
include "biid.mm"
include "eqid.mm"
include "adantr.mm"
include "xp1st.mm"
include "adantl.mm"
include "catidcl.mm"
include "xp2nd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "simpr.mm"
include "xpchom.mm"
include "eleqtrrd.mm"
include "fvex.mm"
include "op1st.mm"
include "oveq1i.mm"
include "simpr1l.mm"
include "syl.mm"
include "simpr1r.mm"
include "simpr31.mm"
include "eleqtrd.mm"
include "catlid.mm"
include "syl5eq.mm"
include "op2nd.mm"
include "opeq12d.mm"
include "syldan.mm"
include "xpcco.mm"
include "1st2nd2.mm"
include "3eqtr4d.mm"
include "oveq2i.mm"
include "simpr2l.mm"
include "simpr32.mm"
include "catrid.mm"
include "catcocl.mm"
include "3eltr4d.mm"
include "simpr2r.mm"
include "simpr33.mm"
include "catass.mm"
include "fveq2d.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "iscatd2.mm"
include "vex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "mpt2mpt.mm"
include "eqeq2i.mm"
include "anbi2i.mm"
include "sylib.mm"

theorem xpccatid
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cT: class T
  let cI: class I
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let cR: class R
  let cS: class S
  assume xpccat.t: |- T = ( C Xc. D )
  assume xpccat.c: |- ( ph -> C e. Cat )
  assume xpccat.d: |- ( ph -> D e. Cat )
  assume xpccat.x: |- X = ( Base ` C )
  assume xpccat.y: |- Y = ( Base ` D )
  assume xpccat.i: |- I = ( Id ` C )
  assume xpccat.j: |- J = ( Id ` D )

  disjoint x y
  disjoint I x
  disjoint I y
  disjoint J x
  disjoint J y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint D x
  disjoint D y
  disjoint Y x
  disjoint Y y
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint I f
  disjoint g h
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint I g
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint I h
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint I s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint I t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint I u
  disjoint v x
  disjoint v y
  disjoint I v
  disjoint J f
  disjoint J g
  disjoint J h
  disjoint J s
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint T f
  disjoint T g
  disjoint T h
  disjoint T s
  disjoint T t
  disjoint T u
  disjoint T v
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint Y f
  disjoint Y g
  disjoint Y h
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  assert |- ( ph -> ( T e. Cat /\ ( Id ` T ) = ( x e. X , y e. Y |-> <. ( I ` x ) , ( J ` y ) >. ) ) )

  proof
    wph
    cT
    ccat
    wcel
    #
    cT
    ccid
    cfv
    #
    vt
    cX
    cY
    cxp
    #
    vt
    cv
    #
    c1st
    cfv
    #
    cI
    cfv
    #
    @3
    c2nd
    cfv
    #
    cJ
    cfv
    #
    cop
    #
    cmpt
    #
    wceq
    #
    wa
    @0
    @1
    vx
    vy
    cX
    cY
    vx
    cv
    #
    cI
    cfv
    #
    vy
    cv
    #
    cJ
    cfv
    #
    cop
    #
    cmpt2
    #
    wceq
    #
    wa
    wph
    vs
    cv
    #
    @2
    wcel
    #
    @3
    @2
    wcel
    #
    wa
    #
    vu
    cv
    #
    @2
    wcel
    #
    vv
    cv
    #
    @2
    wcel
    #
    wa
    #
    vf
    cv
    #
    @18
    @3
    cT
    chom
    cfv
    #
    co
    #
    wcel
    #
    vg
    cv
    #
    @3
    @22
    @28
    co
    #
    wcel
    #
    vh
    cv
    #
    @22
    @24
    @28
    co
    #
    wcel
    #
    w3a
    #
    w3a
    #
    vs
    vt
    vu
    vv
    @2
    cT
    cT
    cco
    cfv
    #
    @8
    vf
    vg
    vh
    @28
    cvv
    @2
    cT
    cbs
    cfv
    wceq
    wph
    cC
    cD
    cT
    cX
    cY
    xpccat.t
    xpccat.x
    xpccat.y
    xpcbas
    #
    a1i
    wph
    @28
    eqidd
    wph
    @39
    eqidd
    cT
    cvv
    wcel
    wph
    cT
    cC
    cD
    cxpc
    co
    cvv
    xpccat.t
    cC
    cD
    cxpc
    ovex
    eqeltri
    a1i
    @38
    biid
    wph
    @20
    wa
    #
    @8
    @4
    @4
    cC
    chom
    cfv
    #
    co
    #
    @6
    @6
    cD
    chom
    cfv
    #
    co
    #
    cxp
    #
    @3
    @3
    @28
    co
    #
    @41
    @5
    @43
    wcel
    @7
    @45
    wcel
    @8
    @46
    wcel
    @41
    cX
    cC
    cI
    @42
    @4
    xpccat.x
    @42
    eqid
    #
    xpccat.i
    wph
    cC
    ccat
    wcel
    #
    @20
    xpccat.c
    adantr
    @20
    @4
    cX
    wcel
    #
    wph
    @3
    cX
    cY
    xp1st
    #
    adantl
    catidcl
    @41
    cY
    cD
    cJ
    @44
    @6
    xpccat.y
    @44
    eqid
    #
    xpccat.j
    wph
    cD
    ccat
    wcel
    #
    @20
    xpccat.d
    adantr
    @20
    @6
    cY
    wcel
    #
    wph
    @3
    cX
    cY
    xp2nd
    #
    adantl
    catidcl
    @5
    @7
    @43
    @45
    opelxpi
    syl2anc
    @41
    @2
    cC
    cD
    cT
    @42
    @44
    @28
    @3
    @3
    xpccat.t
    @40
    @48
    @52
    @28
    eqid
    #
    wph
    @20
    simpr
    #
    @57
    xpchom
    eleqtrrd
    #
    wph
    @38
    wa
    #
    @8
    c1st
    cfv
    #
    @27
    c1st
    cfv
    #
    @18
    c1st
    cfv
    #
    @4
    cop
    #
    @4
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    @8
    c2nd
    cfv
    #
    @27
    c2nd
    cfv
    #
    @18
    c2nd
    cfv
    #
    @6
    cop
    #
    @6
    cD
    cco
    cfv
    #
    co
    #
    co
    #
    cop
    @61
    @68
    cop
    #
    @8
    @27
    @18
    @3
    cop
    #
    @3
    @39
    co
    co
    @27
    @59
    @66
    @61
    @73
    @68
    @59
    @66
    @5
    @61
    @65
    co
    @61
    @60
    @5
    @61
    @65
    @5
    @7
    @4
    cI
    fvex
    #
    @6
    cJ
    fvex
    #
    op1st
    #
    oveq1i
    @59
    cX
    cC
    @64
    cI
    @61
    @42
    @62
    @4
    xpccat.x
    @48
    xpccat.i
    wph
    @49
    @38
    xpccat.c
    adantr
    #
    @59
    @19
    @62
    cX
    wcel
    @19
    @20
    @26
    @37
    wph
    simpr1l
    #
    @18
    cX
    cY
    xp1st
    syl
    #
    @64
    eqid
    #
    @59
    @20
    @50
    @19
    @20
    @26
    @37
    wph
    simpr1r
    #
    @51
    syl
    #
    @59
    @27
    @62
    @4
    @42
    co
    #
    @69
    @6
    @44
    co
    #
    cxp
    #
    wcel
    #
    @61
    @85
    wcel
    @59
    @27
    @29
    @87
    @30
    @33
    @36
    @21
    @26
    wph
    simpr31
    #
    @59
    @2
    cC
    cD
    cT
    @42
    @44
    @28
    @18
    @3
    xpccat.t
    @40
    @48
    @52
    @56
    @80
    @83
    xpchom
    eleqtrd
    #
    @27
    @85
    @86
    xp1st
    syl
    #
    catlid
    syl5eq
    @59
    @73
    @7
    @68
    @72
    co
    @68
    @67
    @7
    @68
    @72
    @5
    @7
    @76
    @77
    op2nd
    #
    oveq1i
    @59
    cY
    cD
    @71
    cJ
    @68
    @44
    @69
    @6
    xpccat.y
    @52
    xpccat.j
    wph
    @53
    @38
    xpccat.d
    adantr
    #
    @59
    @19
    @69
    cY
    wcel
    @80
    @18
    cX
    cY
    xp2nd
    syl
    #
    @71
    eqid
    #
    @59
    @20
    @54
    @83
    @55
    syl
    #
    @59
    @88
    @68
    @86
    wcel
    @90
    @27
    @85
    @86
    xp2nd
    syl
    #
    catlid
    syl5eq
    opeq12d
    @59
    @2
    cC
    cD
    @71
    cT
    @64
    @27
    @8
    @28
    @39
    @18
    @3
    @3
    xpccat.t
    @40
    @56
    @82
    @95
    @39
    eqid
    #
    @80
    @83
    @83
    @89
    wph
    @38
    @20
    @8
    @47
    wcel
    @83
    @58
    syldan
    #
    xpcco
    @59
    @88
    @27
    @74
    wceq
    @90
    @27
    @85
    @86
    1st2nd2
    syl
    3eqtr4d
    @59
    @31
    c1st
    cfv
    #
    @60
    @4
    @4
    cop
    @22
    c1st
    cfv
    #
    @64
    co
    #
    co
    #
    @31
    c2nd
    cfv
    #
    @67
    @6
    @6
    cop
    @22
    c2nd
    cfv
    #
    @71
    co
    #
    co
    #
    cop
    @100
    @104
    cop
    #
    @31
    @8
    @3
    @3
    cop
    @22
    @39
    co
    co
    @31
    @59
    @103
    @100
    @107
    @104
    @59
    @103
    @100
    @5
    @102
    co
    @100
    @60
    @5
    @100
    @102
    @78
    oveq2i
    @59
    cX
    cC
    @64
    cI
    @100
    @42
    @4
    @101
    xpccat.x
    @48
    xpccat.i
    @79
    @84
    @82
    @59
    @23
    @101
    cX
    wcel
    @23
    @25
    @21
    @37
    wph
    simpr2l
    #
    @22
    cX
    cY
    xp1st
    syl
    #
    @59
    @31
    @4
    @101
    @42
    co
    #
    @6
    @105
    @44
    co
    #
    cxp
    #
    wcel
    #
    @100
    @111
    wcel
    @59
    @31
    @32
    @113
    @30
    @33
    @36
    @21
    @26
    wph
    simpr32
    #
    @59
    @2
    cC
    cD
    cT
    @42
    @44
    @28
    @3
    @22
    xpccat.t
    @40
    @48
    @52
    @56
    @83
    @109
    xpchom
    eleqtrd
    #
    @31
    @111
    @112
    xp1st
    syl
    #
    catrid
    syl5eq
    @59
    @107
    @104
    @7
    @106
    co
    @104
    @67
    @7
    @104
    @106
    @92
    oveq2i
    @59
    cY
    cD
    @71
    cJ
    @104
    @44
    @6
    @105
    xpccat.y
    @52
    xpccat.j
    @93
    @96
    @95
    @59
    @23
    @105
    cY
    wcel
    @109
    @22
    cX
    cY
    xp2nd
    syl
    #
    @59
    @114
    @104
    @112
    wcel
    @116
    @31
    @111
    @112
    xp2nd
    syl
    #
    catrid
    syl5eq
    opeq12d
    @59
    @2
    cC
    cD
    @71
    cT
    @64
    @8
    @31
    @28
    @39
    @3
    @3
    @22
    xpccat.t
    @40
    @56
    @82
    @95
    @98
    @83
    @83
    @109
    @99
    @115
    xpcco
    @59
    @114
    @31
    @108
    wceq
    @116
    @31
    @111
    @112
    1st2nd2
    syl
    3eqtr4d
    @59
    @100
    @61
    @63
    @101
    @64
    co
    #
    co
    #
    @104
    @68
    @70
    @105
    @71
    co
    #
    co
    #
    cop
    #
    @62
    @101
    @42
    co
    #
    @69
    @105
    @44
    co
    #
    cxp
    #
    @31
    @27
    @75
    @22
    @39
    co
    co
    #
    @18
    @22
    @28
    co
    @59
    @121
    @125
    wcel
    @123
    @126
    wcel
    @124
    @127
    wcel
    @59
    cX
    cC
    @64
    @61
    @100
    @42
    @62
    @4
    @101
    xpccat.x
    @48
    @82
    @79
    @81
    @84
    @110
    @91
    @117
    catcocl
    @59
    cY
    cD
    @71
    @68
    @104
    @44
    @69
    @6
    @105
    xpccat.y
    @52
    @95
    @93
    @94
    @96
    @118
    @97
    @119
    catcocl
    @121
    @123
    @125
    @126
    opelxpi
    syl2anc
    @59
    @2
    cC
    cD
    @71
    cT
    @64
    @27
    @31
    @28
    @39
    @18
    @3
    @22
    xpccat.t
    @40
    @56
    @82
    @95
    @98
    @80
    @83
    @109
    @89
    @115
    xpcco
    #
    @59
    @2
    cC
    cD
    cT
    @42
    @44
    @28
    @18
    @22
    xpccat.t
    @40
    @48
    @52
    @56
    @80
    @109
    xpchom
    3eltr4d
    #
    @59
    @34
    @31
    @3
    @22
    cop
    @24
    @39
    co
    co
    #
    c1st
    cfv
    #
    @61
    @63
    @24
    c1st
    cfv
    #
    @64
    co
    #
    co
    #
    @131
    c2nd
    cfv
    #
    @68
    @70
    @24
    c2nd
    cfv
    #
    @71
    co
    #
    co
    #
    cop
    @34
    c1st
    cfv
    #
    @128
    c1st
    cfv
    #
    @62
    @101
    cop
    @133
    @64
    co
    #
    co
    #
    @34
    c2nd
    cfv
    #
    @128
    c2nd
    cfv
    #
    @69
    @105
    cop
    @137
    @71
    co
    #
    co
    #
    cop
    @131
    @27
    @75
    @24
    @39
    co
    co
    @34
    @128
    @18
    @22
    cop
    @24
    @39
    co
    co
    @59
    @135
    @143
    @139
    @147
    @59
    @140
    @100
    @4
    @101
    cop
    @133
    @64
    co
    #
    co
    #
    @61
    @134
    co
    @140
    @121
    @142
    co
    @135
    @143
    @59
    cX
    cC
    @64
    @61
    @100
    @42
    @140
    @133
    @62
    @4
    @101
    xpccat.x
    @48
    @82
    @79
    @81
    @84
    @110
    @91
    @117
    @59
    @25
    @133
    cX
    wcel
    @23
    @25
    @21
    @37
    wph
    simpr2r
    #
    @24
    cX
    cY
    xp1st
    syl
    #
    @59
    @34
    @101
    @133
    @42
    co
    #
    @105
    @137
    @44
    co
    #
    cxp
    #
    wcel
    #
    @140
    @152
    wcel
    @59
    @34
    @35
    @154
    @30
    @33
    @36
    @21
    @26
    wph
    simpr33
    #
    @59
    @2
    cC
    cD
    cT
    @42
    @44
    @28
    @22
    @24
    xpccat.t
    @40
    @48
    @52
    @56
    @109
    @150
    xpchom
    eleqtrd
    #
    @34
    @152
    @153
    xp1st
    syl
    #
    catass
    @59
    @132
    @149
    @61
    @134
    @59
    @132
    @149
    @144
    @104
    @6
    @105
    cop
    @137
    @71
    co
    #
    co
    #
    cop
    #
    c1st
    cfv
    @149
    @59
    @131
    @161
    c1st
    @59
    @2
    cC
    cD
    @71
    cT
    @64
    @31
    @34
    @28
    @39
    @3
    @22
    @24
    xpccat.t
    @40
    @56
    @82
    @95
    @98
    @83
    @109
    @150
    @115
    @156
    xpcco
    #
    fveq2d
    @149
    @160
    @140
    @100
    @148
    ovex
    #
    @144
    @104
    @159
    ovex
    #
    op1st
    syl6eq
    oveq1d
    @59
    @141
    @121
    @140
    @142
    @59
    @141
    @124
    c1st
    cfv
    @121
    @59
    @128
    @124
    c1st
    @129
    fveq2d
    @121
    @123
    @100
    @61
    @120
    ovex
    #
    @104
    @68
    @122
    ovex
    #
    op1st
    syl6eq
    oveq2d
    3eqtr4d
    @59
    @160
    @68
    @138
    co
    @144
    @123
    @146
    co
    @139
    @147
    @59
    cY
    cD
    @71
    @68
    @104
    @44
    @144
    @137
    @69
    @6
    @105
    xpccat.y
    @52
    @95
    @93
    @94
    @96
    @118
    @97
    @119
    @59
    @25
    @137
    cY
    wcel
    @150
    @24
    cX
    cY
    xp2nd
    syl
    #
    @59
    @155
    @144
    @153
    wcel
    @157
    @34
    @152
    @153
    xp2nd
    syl
    #
    catass
    @59
    @136
    @160
    @68
    @138
    @59
    @136
    @161
    c2nd
    cfv
    @160
    @59
    @131
    @161
    c2nd
    @162
    fveq2d
    @149
    @160
    @163
    @164
    op2nd
    syl6eq
    oveq1d
    @59
    @145
    @123
    @144
    @146
    @59
    @145
    @124
    c2nd
    cfv
    @123
    @59
    @128
    @124
    c2nd
    @129
    fveq2d
    @121
    @123
    @165
    @166
    op2nd
    syl6eq
    oveq2d
    3eqtr4d
    opeq12d
    @59
    @2
    cC
    cD
    @71
    cT
    @64
    @27
    @131
    @28
    @39
    @18
    @3
    @24
    xpccat.t
    @40
    @56
    @82
    @95
    @98
    @80
    @83
    @150
    @89
    @59
    @161
    @4
    @133
    @42
    co
    #
    @6
    @137
    @44
    co
    #
    cxp
    #
    @131
    @3
    @24
    @28
    co
    @59
    @149
    @169
    wcel
    @160
    @170
    wcel
    @161
    @171
    wcel
    @59
    cX
    cC
    @64
    @100
    @140
    @42
    @4
    @101
    @133
    xpccat.x
    @48
    @82
    @79
    @84
    @110
    @151
    @117
    @158
    catcocl
    @59
    cY
    cD
    @71
    @104
    @144
    @44
    @6
    @105
    @137
    xpccat.y
    @52
    @95
    @93
    @96
    @118
    @167
    @119
    @168
    catcocl
    @149
    @160
    @169
    @170
    opelxpi
    syl2anc
    @162
    @59
    @2
    cC
    cD
    cT
    @42
    @44
    @28
    @3
    @24
    xpccat.t
    @40
    @48
    @52
    @56
    @83
    @150
    xpchom
    3eltr4d
    xpcco
    @59
    @2
    cC
    cD
    @71
    cT
    @64
    @128
    @34
    @28
    @39
    @18
    @22
    @24
    xpccat.t
    @40
    @56
    @82
    @95
    @98
    @80
    @109
    @150
    @130
    @156
    xpcco
    3eqtr4d
    iscatd2
    @10
    @17
    @0
    @9
    @16
    @1
    vx
    vy
    vt
    cX
    cY
    @8
    @15
    @3
    @11
    @13
    cop
    wceq
    #
    @5
    @12
    @7
    @14
    @172
    @4
    @11
    cI
    @11
    @13
    @3
    vx
    vex
    #
    vy
    vex
    #
    op1std
    fveq2d
    @172
    @6
    @13
    cJ
    @11
    @13
    @3
    @173
    @174
    op2ndd
    fveq2d
    opeq12d
    mpt2mpt
    eqeq2i
    anbi2i
    sylib
end
