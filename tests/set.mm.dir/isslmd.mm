include "cslmd.mm"
include "wcel.mm"
include "ccmn.mm"
include "csrg.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "wral.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "cmulr.mm"
include "wsbc.mm"
include "cplusg.mm"
include "cbs.mm"
include "csca.mm"
include "cvsca.mm"
include "fvex.mm"
include "simp1.mm"
include "simp2.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "3anbi3d.mm"
include "simp3.mm"
include "3anbi1d.mm"
include "anbi12d.mm"
include "2ralbidv.mm"
include "raleqbidv.mm"
include "anbi2d.mm"
include "sbc3ie.mm"
include "simpr.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "simpl.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "3anbi123d.mm"
include "syl5bb.mm"
include "sbc2ie.mm"
include "eleq2d.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq12d.mm"
include "df-slmd.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isslmd
  let vx: setvar x
  let vw: setvar w
  let c.pl: class .+
  let c.pd: class .+^
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let cF: class F
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vr: setvar r
  let vq: setvar q
  let va: setvar a
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  let vs: setvar s
  let vt: setvar t
  let vv: setvar v
  let cQ: class Q
  let cR: class R
  let cX: class X
  let cY: class Y
  assume isslmd.v: |- V = ( Base ` W )
  assume isslmd.a: |- .+ = ( +g ` W )
  assume isslmd.s: |- .x. = ( .s ` W )
  assume isslmd.0: |- .0. = ( 0g ` W )
  assume isslmd.f: |- F = ( Scalar ` W )
  assume isslmd.k: |- K = ( Base ` F )
  assume isslmd.p: |- .+^ = ( +g ` F )
  assume isslmd.t: |- .X. = ( .r ` F )
  assume isslmd.u: |- .1. = ( 1r ` F )
  assume isslmd.o: |- O = ( 0g ` F )

  disjoint q r
  disjoint q w
  disjoint q x
  disjoint .X. q
  disjoint r w
  disjoint r x
  disjoint .X. r
  disjoint w x
  disjoint .X. w
  disjoint .X. x
  disjoint .+ q
  disjoint .+ r
  disjoint .+ w
  disjoint .+ x
  disjoint .+^ q
  disjoint .+^ r
  disjoint .+^ w
  disjoint .+^ x
  disjoint .1. q
  disjoint .1. r
  disjoint .1. w
  disjoint .1. x
  disjoint .x. q
  disjoint .x. r
  disjoint .x. w
  disjoint .x. x
  disjoint F q
  disjoint F r
  disjoint F w
  disjoint F x
  disjoint K q
  disjoint K r
  disjoint K w
  disjoint K x
  disjoint V q
  disjoint V r
  disjoint V w
  disjoint V x
  disjoint W q
  disjoint W r
  disjoint W w
  disjoint W x
  disjoint .0. q
  disjoint .0. r
  disjoint .0. w
  disjoint .0. x
  disjoint O q
  disjoint O r
  disjoint O w
  disjoint O x
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a p
  disjoint a q
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint .X. a
  disjoint f g
  disjoint f k
  disjoint f p
  disjoint f q
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint .X. f
  disjoint g k
  disjoint g p
  disjoint g q
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint .X. g
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint .X. k
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint .X. p
  disjoint q s
  disjoint q t
  disjoint q v
  disjoint r s
  disjoint r t
  disjoint r v
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint .X. s
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint .X. t
  disjoint v w
  disjoint v x
  disjoint .X. v
  disjoint .+ a
  disjoint .+ f
  disjoint .+ g
  disjoint .+ k
  disjoint .+ p
  disjoint .+ s
  disjoint .+ v
  disjoint .+^ a
  disjoint .+^ f
  disjoint .+^ g
  disjoint .+^ k
  disjoint .+^ p
  disjoint .+^ s
  disjoint .+^ v
  disjoint .1. a
  disjoint .1. f
  disjoint .1. g
  disjoint .1. k
  disjoint .1. p
  disjoint .1. s
  disjoint .1. v
  disjoint .x. a
  disjoint .x. f
  disjoint .x. g
  disjoint .x. k
  disjoint .x. p
  disjoint .x. s
  disjoint .x. v
  disjoint F a
  disjoint F f
  disjoint F g
  disjoint F k
  disjoint F p
  disjoint F s
  disjoint F t
  disjoint F v
  disjoint K a
  disjoint K f
  disjoint K g
  disjoint K k
  disjoint K p
  disjoint K s
  disjoint K v
  disjoint V a
  disjoint V f
  disjoint V g
  disjoint V k
  disjoint V p
  disjoint V s
  disjoint V v
  disjoint W a
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint W v
  disjoint .0. g
  disjoint O g
  disjoint Q q
  disjoint Q r
  disjoint Q w
  disjoint Q x
  disjoint R r
  disjoint R w
  disjoint R x
  disjoint X w
  disjoint X x
  disjoint Y w
  assert |- ( W e. SLMod <-> ( W e. CMnd /\ F e. SRing /\ A. q e. K A. r e. K A. x e. V A. w e. V ( ( ( r .x. w ) e. V /\ ( r .x. ( w .+ x ) ) = ( ( r .x. w ) .+ ( r .x. x ) ) /\ ( ( q .+^ r ) .x. w ) = ( ( q .x. w ) .+ ( r .x. w ) ) ) /\ ( ( ( q .X. r ) .x. w ) = ( q .x. ( r .x. w ) ) /\ ( .1. .x. w ) = w /\ ( O .x. w ) = .0. ) ) ) )

  proof
    cW
    cslmd
    wcel
    cW
    ccmn
    wcel
    #
    cF
    csrg
    wcel
    #
    vr
    cv
    #
    vw
    cv
    #
    c.x
    co
    #
    cV
    wcel
    #
    @2
    @3
    vx
    cv
    #
    c.pl
    co
    #
    c.x
    co
    #
    @4
    @2
    @6
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vq
    cv
    #
    @2
    c.pd
    co
    #
    @3
    c.x
    co
    #
    @12
    @3
    c.x
    co
    #
    @4
    c.pl
    co
    #
    wceq
    #
    w3a
    #
    @12
    @2
    c.xp
    co
    #
    @3
    c.x
    co
    #
    @12
    @4
    c.x
    co
    #
    wceq
    #
    c.1
    @3
    c.x
    co
    #
    @3
    wceq
    #
    cO
    @3
    c.x
    co
    #
    c.0
    wceq
    #
    w3a
    #
    wa
    #
    vw
    cV
    wral
    #
    vx
    cV
    wral
    #
    vr
    cK
    wral
    #
    vq
    cK
    wral
    #
    wa
    #
    wa
    @0
    @1
    @32
    w3a
    vf
    cv
    #
    csrg
    wcel
    #
    @2
    @3
    vs
    cv
    #
    co
    #
    vv
    cv
    #
    wcel
    #
    @2
    @3
    @6
    va
    cv
    #
    co
    #
    @36
    co
    #
    @37
    @2
    @6
    @36
    co
    #
    @40
    co
    #
    wceq
    #
    @12
    @2
    vp
    cv
    #
    co
    #
    @3
    @36
    co
    #
    @12
    @3
    @36
    co
    #
    @37
    @40
    co
    #
    wceq
    #
    w3a
    #
    @12
    @2
    vt
    cv
    #
    co
    #
    @3
    @36
    co
    #
    @12
    @37
    @36
    co
    #
    wceq
    #
    @34
    cur
    cfv
    #
    @3
    @36
    co
    #
    @3
    wceq
    #
    @34
    c0g
    cfv
    #
    @3
    @36
    co
    #
    vg
    cv
    #
    c0g
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    #
    vw
    @38
    wral
    vx
    @38
    wral
    #
    vr
    vk
    cv
    #
    wral
    #
    vq
    @69
    wral
    #
    wa
    #
    vt
    @34
    cmulr
    cfv
    #
    wsbc
    vp
    @34
    cplusg
    cfv
    #
    wsbc
    vk
    @34
    cbs
    cfv
    #
    wsbc
    #
    vf
    @63
    csca
    cfv
    #
    wsbc
    vs
    @63
    cvsca
    cfv
    #
    wsbc
    #
    va
    @63
    cplusg
    cfv
    #
    wsbc
    vv
    @63
    cbs
    cfv
    #
    wsbc
    #
    @33
    vg
    cW
    ccmn
    cslmd
    @82
    @77
    csrg
    wcel
    #
    @2
    @3
    @78
    co
    #
    @81
    wcel
    #
    @2
    @3
    @6
    @80
    co
    #
    @78
    co
    #
    @84
    @2
    @6
    @78
    co
    #
    @80
    co
    #
    wceq
    #
    @12
    @2
    @77
    cplusg
    cfv
    #
    co
    #
    @3
    @78
    co
    #
    @12
    @3
    @78
    co
    #
    @84
    @80
    co
    #
    wceq
    #
    w3a
    #
    @12
    @2
    @77
    cmulr
    cfv
    #
    co
    #
    @3
    @78
    co
    #
    @12
    @84
    @78
    co
    #
    wceq
    #
    @77
    cur
    cfv
    #
    @3
    @78
    co
    #
    @3
    wceq
    #
    @77
    c0g
    cfv
    #
    @3
    @78
    co
    #
    @64
    wceq
    #
    w3a
    #
    wa
    #
    vw
    @81
    wral
    #
    vx
    @81
    wral
    #
    vr
    @77
    cbs
    cfv
    #
    wral
    #
    vq
    @113
    wral
    #
    wa
    #
    @63
    cW
    wceq
    #
    @33
    @79
    @116
    vv
    va
    @81
    @80
    @63
    cbs
    fvex
    @63
    cplusg
    fvex
    @79
    @83
    @84
    @38
    wcel
    #
    @2
    @41
    @78
    co
    #
    @84
    @88
    @40
    co
    #
    wceq
    #
    @93
    @94
    @84
    @40
    co
    #
    wceq
    #
    w3a
    #
    @109
    wa
    #
    vw
    @38
    wral
    #
    vx
    @38
    wral
    #
    vr
    @113
    wral
    #
    vq
    @113
    wral
    #
    wa
    #
    @38
    @81
    wceq
    #
    @40
    @80
    wceq
    #
    wa
    #
    @116
    @76
    @130
    vs
    vf
    @78
    @77
    @63
    cvsca
    fvex
    @63
    csca
    fvex
    @76
    @35
    @39
    @45
    @12
    @2
    @74
    co
    #
    @3
    @36
    co
    #
    @50
    wceq
    #
    w3a
    #
    @12
    @2
    @73
    co
    #
    @3
    @36
    co
    #
    @56
    wceq
    #
    @60
    @65
    w3a
    #
    wa
    #
    vw
    @38
    wral
    vx
    @38
    wral
    #
    vr
    @75
    wral
    #
    vq
    @75
    wral
    #
    wa
    #
    @36
    @78
    wceq
    #
    @34
    @77
    wceq
    #
    wa
    #
    @130
    @72
    @146
    vk
    vp
    vt
    @75
    @74
    @73
    @34
    cbs
    fvex
    @34
    cplusg
    fvex
    @34
    cmulr
    fvex
    @69
    @75
    wceq
    #
    @46
    @74
    wceq
    #
    @53
    @73
    wceq
    #
    w3a
    #
    @71
    @145
    @35
    @153
    @70
    @144
    vq
    @69
    @75
    @150
    @151
    @152
    simp1
    #
    @153
    @68
    @143
    vr
    @69
    @75
    @154
    @153
    @67
    @142
    vx
    vw
    @38
    @38
    @153
    @52
    @137
    @66
    @141
    @153
    @51
    @136
    @39
    @45
    @153
    @48
    @135
    @50
    @153
    @47
    @134
    @3
    @36
    @153
    @46
    @74
    @12
    @2
    @150
    @151
    @152
    simp2
    oveqd
    oveq1d
    eqeq1d
    3anbi3d
    @153
    @57
    @140
    @60
    @65
    @153
    @55
    @139
    @56
    @153
    @54
    @138
    @3
    @36
    @153
    @53
    @73
    @12
    @2
    @150
    @151
    @152
    simp3
    oveqd
    oveq1d
    eqeq1d
    3anbi1d
    anbi12d
    2ralbidv
    raleqbidv
    raleqbidv
    anbi2d
    sbc3ie
    @149
    @35
    @83
    @145
    @129
    @149
    @34
    @77
    csrg
    @147
    @148
    simpr
    #
    eleq1d
    @149
    @144
    @128
    vq
    @75
    @113
    @149
    @34
    @77
    cbs
    @155
    fveq2d
    #
    @149
    @143
    @127
    vr
    @75
    @113
    @156
    @149
    @142
    @125
    vx
    vw
    @38
    @38
    @149
    @137
    @124
    @141
    @109
    @149
    @39
    @118
    @45
    @121
    @136
    @123
    @149
    @37
    @84
    @38
    @149
    @36
    @78
    @2
    @3
    @147
    @148
    simpl
    #
    oveqd
    #
    eleq1d
    @149
    @42
    @119
    @44
    @120
    @149
    @36
    @78
    @2
    @41
    @157
    oveqd
    @149
    @37
    @84
    @43
    @88
    @40
    @158
    @149
    @36
    @78
    @2
    @6
    @157
    oveqd
    oveq12d
    eqeq12d
    @149
    @135
    @93
    @50
    @122
    @149
    @134
    @92
    @3
    @3
    @36
    @78
    @157
    @149
    @74
    @91
    @12
    @2
    @149
    @34
    @77
    cplusg
    @155
    fveq2d
    oveqd
    @149
    @3
    eqidd
    #
    oveq123d
    @149
    @49
    @94
    @37
    @84
    @40
    @149
    @36
    @78
    @12
    @3
    @157
    oveqd
    @158
    oveq12d
    eqeq12d
    3anbi123d
    @149
    @140
    @102
    @60
    @105
    @65
    @108
    @149
    @139
    @100
    @56
    @101
    @149
    @138
    @99
    @3
    @3
    @36
    @78
    @157
    @149
    @73
    @98
    @12
    @2
    @149
    @34
    @77
    cmulr
    @155
    fveq2d
    oveqd
    @159
    oveq123d
    @149
    @12
    @12
    @37
    @84
    @36
    @78
    @157
    @149
    @12
    eqidd
    @158
    oveq123d
    eqeq12d
    @149
    @59
    @104
    @3
    @149
    @58
    @103
    @3
    @3
    @36
    @78
    @157
    @149
    @34
    @77
    cur
    @155
    fveq2d
    @159
    oveq123d
    eqeq1d
    @149
    @62
    @107
    @64
    @149
    @61
    @106
    @3
    @3
    @36
    @78
    @157
    @149
    @34
    @77
    c0g
    @155
    fveq2d
    @159
    oveq123d
    eqeq1d
    3anbi123d
    anbi12d
    2ralbidv
    raleqbidv
    raleqbidv
    anbi12d
    syl5bb
    sbc2ie
    @133
    @129
    @115
    @83
    @133
    @127
    @112
    vq
    vr
    @113
    @113
    @133
    @126
    @111
    vx
    @38
    @81
    @131
    @132
    simpl
    #
    @133
    @125
    @110
    vw
    @38
    @81
    @160
    @133
    @124
    @97
    @109
    @133
    @118
    @85
    @121
    @90
    @123
    @96
    @133
    @38
    @81
    @84
    @160
    eleq2d
    @133
    @119
    @87
    @120
    @89
    @133
    @41
    @86
    @2
    @78
    @133
    @40
    @80
    @3
    @6
    @131
    @132
    simpr
    #
    oveqd
    oveq2d
    @133
    @40
    @80
    @84
    @88
    @161
    oveqd
    eqeq12d
    @133
    @122
    @95
    @93
    @133
    @40
    @80
    @94
    @84
    @161
    oveqd
    eqeq2d
    3anbi123d
    anbi1d
    raleqbidv
    raleqbidv
    2ralbidv
    anbi2d
    syl5bb
    sbc2ie
    @117
    @83
    @1
    @115
    @32
    @117
    @77
    cF
    csrg
    @117
    @77
    cW
    csca
    cfv
    cF
    @63
    cW
    csca
    fveq2
    isslmd.f
    syl6eqr
    #
    eleq1d
    @117
    @114
    @31
    vq
    @113
    cK
    @117
    @113
    cF
    cbs
    cfv
    cK
    @117
    @77
    cF
    cbs
    @162
    fveq2d
    isslmd.k
    syl6eqr
    #
    @117
    @112
    @30
    vr
    @113
    cK
    @163
    @117
    @111
    @29
    vx
    @81
    cV
    @117
    @81
    cW
    cbs
    cfv
    cV
    @63
    cW
    cbs
    fveq2
    isslmd.v
    syl6eqr
    #
    @117
    @110
    @28
    vw
    @81
    cV
    @164
    @117
    @97
    @18
    @109
    @27
    @117
    @85
    @5
    @90
    @11
    @96
    @17
    @117
    @84
    @4
    @81
    cV
    @117
    @78
    c.x
    @2
    @3
    @117
    @78
    cW
    cvsca
    cfv
    c.x
    @63
    cW
    cvsca
    fveq2
    isslmd.s
    syl6eqr
    #
    oveqd
    #
    @164
    eleq12d
    @117
    @87
    @8
    @89
    @10
    @117
    @2
    @2
    @86
    @7
    @78
    c.x
    @165
    @117
    @2
    eqidd
    @117
    @80
    c.pl
    @3
    @6
    @117
    @80
    cW
    cplusg
    cfv
    c.pl
    @63
    cW
    cplusg
    fveq2
    isslmd.a
    syl6eqr
    #
    oveqd
    oveq123d
    @117
    @84
    @4
    @88
    @9
    @80
    c.pl
    @167
    @166
    @117
    @78
    c.x
    @2
    @6
    @165
    oveqd
    oveq123d
    eqeq12d
    @117
    @93
    @14
    @95
    @16
    @117
    @92
    @13
    @3
    @3
    @78
    c.x
    @165
    @117
    @91
    c.pd
    @12
    @2
    @117
    @91
    cF
    cplusg
    cfv
    c.pd
    @117
    @77
    cF
    cplusg
    @162
    fveq2d
    isslmd.p
    syl6eqr
    oveqd
    @117
    @3
    eqidd
    #
    oveq123d
    @117
    @94
    @15
    @84
    @4
    @80
    c.pl
    @167
    @117
    @78
    c.x
    @12
    @3
    @165
    oveqd
    @166
    oveq123d
    eqeq12d
    3anbi123d
    @117
    @102
    @22
    @105
    @24
    @108
    @26
    @117
    @100
    @20
    @101
    @21
    @117
    @99
    @19
    @3
    @3
    @78
    c.x
    @165
    @117
    @98
    c.xp
    @12
    @2
    @117
    @98
    cF
    cmulr
    cfv
    c.xp
    @117
    @77
    cF
    cmulr
    @162
    fveq2d
    isslmd.t
    syl6eqr
    oveqd
    @168
    oveq123d
    @117
    @12
    @12
    @84
    @4
    @78
    c.x
    @165
    @117
    @12
    eqidd
    @166
    oveq123d
    eqeq12d
    @117
    @104
    @23
    @3
    @117
    @103
    c.1
    @3
    @3
    @78
    c.x
    @165
    @117
    @103
    cF
    cur
    cfv
    c.1
    @117
    @77
    cF
    cur
    @162
    fveq2d
    isslmd.u
    syl6eqr
    @168
    oveq123d
    eqeq1d
    @117
    @107
    @25
    @64
    c.0
    @117
    @106
    cO
    @3
    @3
    @78
    c.x
    @165
    @117
    @106
    cF
    c0g
    cfv
    cO
    @117
    @77
    cF
    c0g
    @162
    fveq2d
    isslmd.o
    syl6eqr
    @168
    oveq123d
    @117
    @64
    cW
    c0g
    cfv
    c.0
    @63
    cW
    c0g
    fveq2
    isslmd.0
    syl6eqr
    eqeq12d
    3anbi123d
    anbi12d
    raleqbidv
    raleqbidv
    raleqbidv
    raleqbidv
    anbi12d
    syl5bb
    vx
    vw
    vv
    vt
    vf
    vg
    vk
    vs
    vr
    vq
    vp
    va
    df-slmd
    elrab2
    @0
    @1
    @32
    3anass
    bitr4i
end
