include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "c1st.mm"
include "co.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "c0g.mm"
include "csg.mm"
include "cmpd.mm"
include "wsbc.mm"
include "clspn.mm"
include "cbs.mm"
include "clcd.mm"
include "cdvh.mm"
include "cab.mm"
include "chdma1.mm"
include "hdmap1ffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "sbceq1d.mm"
include "sbcbidv.mm"
include "sbceqbid.mm"
include "fvex.mm"
include "w3a.mm"
include "wb.mm"
include "eqeq2i.mm"
include "biimpri.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "syl6eqr.mm"
include "simp3.mm"
include "id.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "riotabidv.mm"
include "ifeq2d.mm"
include "mpteq2dv.mm"
include "eleq2d.mm"
include "syl.mm"
include "sbcie.mm"
include "xpeq2.mm"
include "xpeq1d.mm"
include "simp1.mm"
include "eqeq2d.mm"
include "oveqd.mm"
include "sneqd.mm"
include "fveq12d.mm"
include "riotaeqbidv.mm"
include "ifeq12d.mm"
include "mpteq12dv.mm"
include "syl5bb.mm"
include "syl3anc.mm"
include "sbc3ie.mm"
include "xpeq12d.mm"
include "ifbieq2d.mm"
include "syl6bb.mm"
include "abbi1dv.mm"
include "eqid.mm"
include "cvv.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem hdmap1fval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  let vw: setvar w
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  assume hdmap1val.h: |- H = ( LHyp ` K )
  assume hdmap1fval.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1fval.v: |- V = ( Base ` U )
  assume hdmap1fval.s: |- .- = ( -g ` U )
  assume hdmap1fval.o: |- .0. = ( 0g ` U )
  assume hdmap1fval.n: |- N = ( LSpan ` U )
  assume hdmap1fval.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1fval.d: |- D = ( Base ` C )
  assume hdmap1fval.r: |- R = ( -g ` C )
  assume hdmap1fval.q: |- Q = ( 0g ` C )
  assume hdmap1fval.j: |- J = ( LSpan ` C )
  assume hdmap1fval.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1fval.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1fval.k: |- ( ph -> ( K e. A /\ W e. H ) )

  disjoint h x
  disjoint C h
  disjoint C x
  disjoint D h
  disjoint D x
  disjoint J h
  disjoint J x
  disjoint M h
  disjoint M x
  disjoint N h
  disjoint N x
  disjoint U h
  disjoint U x
  disjoint V h
  disjoint V x
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint a c
  disjoint a d
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint K a
  disjoint c d
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint K c
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint K d
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint K j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint K k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint K m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint K n
  disjoint u v
  disjoint u w
  disjoint K u
  disjoint v w
  disjoint K v
  disjoint K w
  disjoint a h
  disjoint a x
  disjoint c h
  disjoint c x
  disjoint d h
  disjoint d x
  disjoint h j
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint j x
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint D a
  disjoint D c
  disjoint D d
  disjoint D j
  disjoint D n
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint J a
  disjoint J c
  disjoint J d
  disjoint J j
  disjoint J n
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint M a
  disjoint M c
  disjoint M d
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint N a
  disjoint N n
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint .0. a
  disjoint .0. n
  disjoint .0. u
  disjoint .0. v
  disjoint .0. w
  disjoint Q a
  disjoint Q c
  disjoint Q d
  disjoint Q j
  disjoint Q n
  disjoint Q u
  disjoint Q v
  disjoint Q w
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R j
  disjoint R n
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint .- a
  disjoint .- n
  disjoint .- u
  disjoint .- v
  disjoint .- w
  disjoint V a
  disjoint V n
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint W a
  disjoint W c
  disjoint W d
  disjoint W j
  disjoint W m
  disjoint W n
  disjoint W u
  disjoint W v
  disjoint W w
  assert |- ( ph -> I = ( x e. ( ( V X. D ) X. V ) |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) ) )

  proof
    wph
    cK
    cA
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cI
    vx
    cV
    cD
    cxp
    #
    cV
    cxp
    #
    vx
    cv
    #
    c2nd
    cfv
    #
    c.0
    wceq
    #
    cQ
    @5
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    vh
    cv
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    @4
    c1st
    cfv
    #
    c1st
    cfv
    #
    @5
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @14
    c2nd
    cfv
    #
    @10
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    vh
    cD
    crio
    #
    cif
    #
    cmpt
    #
    wceq
    hdmap1fval.k
    @0
    @1
    cI
    cW
    vw
    cH
    va
    cv
    #
    vx
    vv
    cv
    #
    vd
    cv
    #
    cxp
    #
    @30
    cxp
    #
    @5
    vu
    cv
    #
    c0g
    cfv
    #
    wceq
    #
    vc
    cv
    #
    c0g
    cfv
    #
    @7
    vn
    cv
    #
    cfv
    #
    vm
    cv
    #
    cfv
    #
    @11
    vj
    cv
    #
    cfv
    #
    wceq
    #
    @15
    @5
    @34
    csg
    cfv
    #
    co
    #
    csn
    #
    @39
    cfv
    #
    @41
    cfv
    #
    @20
    @10
    @37
    csg
    cfv
    #
    co
    #
    csn
    #
    @43
    cfv
    #
    wceq
    #
    wa
    #
    vh
    @31
    crio
    #
    cif
    #
    cmpt
    #
    wcel
    #
    vm
    vw
    cv
    #
    cK
    cmpd
    cfv
    #
    cfv
    #
    wsbc
    #
    vj
    @37
    clspn
    cfv
    #
    wsbc
    #
    vd
    @37
    cbs
    cfv
    #
    wsbc
    #
    vc
    @61
    cK
    clcd
    cfv
    #
    cfv
    #
    wsbc
    #
    vn
    @34
    clspn
    cfv
    #
    wsbc
    #
    vv
    @34
    cbs
    cfv
    #
    wsbc
    #
    vu
    @61
    cK
    cdvh
    cfv
    #
    cfv
    #
    wsbc
    #
    va
    cab
    #
    cmpt
    #
    cfv
    #
    @28
    @0
    cI
    cW
    cK
    chdma1
    cfv
    #
    cfv
    @81
    hdmap1fval.i
    @0
    cW
    @82
    @80
    vx
    vw
    vv
    vu
    vh
    vj
    vm
    vn
    cH
    cK
    cA
    va
    vc
    vd
    hdmap1val.h
    hdmap1ffval
    fveq1d
    syl5eq
    vw
    cW
    @79
    @28
    cH
    @80
    @61
    cW
    wceq
    #
    @78
    va
    @28
    @83
    @78
    @60
    vm
    cW
    @62
    cfv
    #
    wsbc
    #
    vj
    @65
    wsbc
    #
    vd
    @67
    wsbc
    #
    vc
    cW
    @69
    cfv
    #
    wsbc
    #
    vn
    @72
    wsbc
    #
    vv
    @74
    wsbc
    #
    vu
    cW
    @76
    cfv
    #
    wsbc
    @29
    @28
    wcel
    #
    @83
    @75
    @91
    vu
    @77
    @92
    @61
    cW
    @76
    fveq2
    @83
    @73
    @90
    vv
    @74
    @83
    @71
    @89
    vn
    @72
    @83
    @68
    @87
    vc
    @70
    @88
    @61
    cW
    @69
    fveq2
    @83
    @66
    @86
    vd
    @67
    @83
    @64
    @85
    vj
    @65
    @83
    @60
    vm
    @63
    @84
    @61
    cW
    @62
    fveq2
    sbceq1d
    sbcbidv
    sbcbidv
    sbceqbid
    sbcbidv
    sbcbidv
    sbceqbid
    @89
    @93
    vu
    vv
    vn
    @92
    @74
    @72
    cW
    @76
    fvex
    @34
    cbs
    fvex
    @34
    clspn
    fvex
    @34
    @92
    wceq
    #
    @30
    @74
    wceq
    #
    @39
    @72
    wceq
    #
    w3a
    #
    @34
    cU
    wceq
    #
    @30
    cV
    wceq
    #
    @39
    cN
    wceq
    #
    @89
    @93
    wb
    @94
    @95
    @98
    @96
    @98
    @94
    cU
    @92
    @34
    hdmap1fval.u
    eqeq2i
    biimpri
    #
    3ad2ant1
    #
    @97
    @30
    cU
    cbs
    cfv
    #
    cV
    @97
    @30
    @74
    @103
    @94
    @95
    @96
    simp2
    @94
    @95
    @74
    @103
    wceq
    @96
    @94
    @34
    cU
    cbs
    @101
    fveq2d
    3ad2ant1
    eqtrd
    hdmap1fval.v
    syl6eqr
    @97
    @39
    cU
    clspn
    cfv
    #
    cN
    @97
    @39
    @72
    @104
    @94
    @95
    @96
    simp3
    @97
    @34
    cU
    clspn
    @102
    fveq2d
    eqtrd
    hdmap1fval.n
    syl6eqr
    @89
    @29
    vx
    @30
    cD
    cxp
    #
    @30
    cxp
    #
    @36
    cQ
    @40
    cM
    cfv
    #
    @12
    wceq
    #
    @49
    cM
    cfv
    #
    @23
    wceq
    #
    wa
    #
    vh
    cD
    crio
    #
    cif
    #
    cmpt
    #
    wcel
    #
    @98
    @99
    @100
    w3a
    #
    @93
    @85
    @115
    vc
    vd
    vj
    @88
    @67
    @65
    cW
    @69
    fvex
    @37
    cbs
    fvex
    @37
    clspn
    fvex
    @37
    @88
    wceq
    #
    @31
    @67
    wceq
    #
    @43
    @65
    wceq
    #
    w3a
    #
    @37
    cC
    wceq
    #
    @31
    cD
    wceq
    #
    @43
    cJ
    wceq
    #
    @85
    @115
    wb
    @117
    @118
    @121
    @119
    @117
    @37
    @88
    cC
    @117
    id
    hdmap1fval.c
    syl6eqr
    3ad2ant1
    #
    @120
    @31
    @67
    cD
    @117
    @118
    @119
    simp2
    @120
    @67
    cC
    cbs
    cfv
    #
    cD
    @120
    @37
    cC
    cbs
    @124
    fveq2d
    hdmap1fval.d
    syl6eqr
    eqtrd
    @120
    @43
    @65
    cJ
    @117
    @118
    @119
    simp3
    @120
    @65
    cC
    clspn
    cfv
    cJ
    @120
    @37
    cC
    clspn
    @124
    fveq2d
    hdmap1fval.j
    syl6eqr
    eqtrd
    @85
    @29
    vx
    @33
    @36
    @38
    @107
    @44
    wceq
    #
    @109
    @54
    wceq
    #
    wa
    #
    vh
    @31
    crio
    #
    cif
    #
    cmpt
    #
    wcel
    #
    @121
    @122
    @123
    w3a
    #
    @115
    @60
    @132
    vm
    @84
    cW
    @62
    fvex
    @41
    @84
    wceq
    #
    @41
    cM
    wceq
    #
    @60
    @132
    wb
    @134
    @41
    @84
    cM
    @134
    id
    hdmap1fval.m
    syl6eqr
    @135
    @59
    @131
    @29
    @135
    vx
    @33
    @58
    @130
    @135
    @36
    @57
    @129
    @38
    @135
    @56
    @128
    vh
    @31
    @135
    @45
    @126
    @55
    @127
    @135
    @42
    @107
    @44
    @40
    @41
    cM
    fveq1
    eqeq1d
    @135
    @50
    @109
    @54
    @49
    @41
    cM
    fveq1
    eqeq1d
    anbi12d
    riotabidv
    ifeq2d
    mpteq2dv
    eleq2d
    syl
    sbcie
    @133
    @131
    @114
    @29
    @133
    vx
    @33
    @130
    @106
    @113
    @133
    @122
    @33
    @106
    wceq
    @121
    @122
    @123
    simp2
    #
    @122
    @32
    @105
    @30
    @31
    cD
    @30
    xpeq2
    xpeq1d
    syl
    @133
    @36
    @38
    cQ
    @129
    @112
    @133
    @38
    cC
    c0g
    cfv
    cQ
    @133
    @37
    cC
    c0g
    @121
    @122
    @123
    simp1
    #
    fveq2d
    hdmap1fval.q
    syl6eqr
    @133
    @128
    @111
    vh
    @31
    cD
    @136
    @133
    @126
    @108
    @127
    @110
    @133
    @44
    @12
    @107
    @133
    @11
    @43
    cJ
    @121
    @122
    @123
    simp3
    #
    fveq1d
    eqeq2d
    @133
    @54
    @23
    @109
    @133
    @53
    @22
    @43
    cJ
    @138
    @133
    @52
    @21
    @133
    @51
    cR
    @20
    @10
    @133
    @51
    cC
    csg
    cfv
    cR
    @133
    @37
    cC
    csg
    @137
    fveq2d
    hdmap1fval.r
    syl6eqr
    oveqd
    sneqd
    fveq12d
    eqeq2d
    anbi12d
    riotaeqbidv
    ifeq12d
    mpteq12dv
    eleq2d
    syl5bb
    syl3anc
    sbc3ie
    @116
    @114
    @28
    @29
    @116
    vx
    @106
    @113
    @3
    @27
    @116
    @105
    @2
    @30
    cV
    @116
    @30
    cV
    cD
    @98
    @99
    @100
    simp2
    #
    xpeq1d
    @139
    xpeq12d
    @116
    @36
    @6
    @112
    @26
    cQ
    @116
    @35
    c.0
    @5
    @116
    @35
    cU
    c0g
    cfv
    c.0
    @116
    @34
    cU
    c0g
    @98
    @99
    @100
    simp1
    #
    fveq2d
    hdmap1fval.o
    syl6eqr
    eqeq2d
    @116
    @111
    @25
    vh
    cD
    @116
    @108
    @13
    @110
    @24
    @116
    @107
    @9
    @12
    @116
    @40
    @8
    cM
    @116
    @7
    @39
    cN
    @98
    @99
    @100
    simp3
    #
    fveq1d
    fveq2d
    eqeq1d
    @116
    @109
    @19
    @23
    @116
    @49
    @18
    cM
    @116
    @48
    @17
    @39
    cN
    @141
    @116
    @47
    @16
    @116
    @46
    c.mi
    @15
    @5
    @116
    @46
    cU
    csg
    cfv
    c.mi
    @116
    @34
    cU
    csg
    @140
    fveq2d
    hdmap1fval.s
    syl6eqr
    oveqd
    sneqd
    fveq12d
    fveq2d
    eqeq1d
    anbi12d
    riotabidv
    ifbieq2d
    mpteq12dv
    eleq2d
    syl5bb
    syl3anc
    sbc3ie
    syl6bb
    abbi1dv
    @80
    eqid
    vx
    @3
    @27
    @2
    cV
    cV
    cD
    cV
    @103
    cvv
    hdmap1fval.v
    cU
    cbs
    fvex
    eqeltri
    #
    cD
    @125
    cvv
    hdmap1fval.d
    cC
    cbs
    fvex
    eqeltri
    xpex
    @142
    xpex
    mptex
    fvmpt
    sylan9eq
    syl
end
