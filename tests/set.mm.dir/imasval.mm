include "cimas.mm"
include "co.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cip.mm"
include "cun.mm"
include "cts.mm"
include "cple.mm"
include "cds.mm"
include "cvv.mm"
include "cv.mm"
include "crn.mm"
include "csn.mm"
include "ciun.mm"
include "cmpt2.mm"
include "ctopn.mm"
include "cqtop.mm"
include "ccom.mm"
include "ccnv.mm"
include "cn.mm"
include "c1.mm"
include "c1st.mm"
include "wceq.mm"
include "c2nd.mm"
include "caddc.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "w3a.mm"
include "cxp.mm"
include "cmap.mm"
include "crab.mm"
include "cxrs.mm"
include "cgsu.mm"
include "cmpt.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "csb.mm"
include "df-imas.mm"
include "a1i.mm"
include "wa.mm"
include "fvexd.mm"
include "simplrl.mm"
include "rneqd.mm"
include "wfo.mm"
include "forn.mm"
include "syl.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "opeq2d.mm"
include "simplrr.mm"
include "fveq2d.mm"
include "simpr.mm"
include "3eqtr4d.mm"
include "fveq1d.mm"
include "opeq12d.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "fveq12d.mm"
include "sneqd.mm"
include "iuneq12d.mm"
include "eqtr4d.mm"
include "tpeq123d.mm"
include "mpt2eq123dv.mm"
include "iuneq2d.mm"
include "iuneq1d.mm"
include "uneq12d.mm"
include "oveq12d.mm"
include "coeq12d.mm"
include "cnveqd.mm"
include "sqxpeqd.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "rabeqbidv.mm"
include "coeq1d.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "infeq1d.mm"
include "csbied.mm"
include "wf.mm"
include "wcel.mm"
include "fof.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "fex.mm"
include "syl2anc.mm"
include "elex.mm"
include "tpex.mm"
include "unex.mm"
include "ovmpt2d.mm"

theorem imasval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let c.xp: class .X.
  let c.xo: class .(x)
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let c.xi: class .,
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cO: class O
  let cV: class V
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let vf: setvar f
  let vr: setvar r
  let vv: setvar v
  assume imasval.u: |- ( ph -> U = ( F "s R ) )
  assume imasval.v: |- ( ph -> V = ( Base ` R ) )
  assume imasval.p: |- .+ = ( +g ` R )
  assume imasval.m: |- .X. = ( .r ` R )
  assume imasval.g: |- G = ( Scalar ` R )
  assume imasval.k: |- K = ( Base ` G )
  assume imasval.q: |- .x. = ( .s ` R )
  assume imasval.i: |- ., = ( .i ` R )
  assume imasval.j: |- J = ( TopOpen ` R )
  assume imasval.e: |- E = ( dist ` R )
  assume imasval.n: |- N = ( le ` R )
  assume imasval.a: |- ( ph -> .+b = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .+ q ) ) >. } )
  assume imasval.t: |- ( ph -> .xb = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .X. q ) ) >. } )
  assume imasval.s: |- ( ph -> .(x) = U_ q e. V ( p e. K , x e. { ( F ` q ) } |-> ( F ` ( p .x. q ) ) ) )
  assume imasval.w: |- ( ph -> I = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( p ., q ) >. } )
  assume imasval.o: |- ( ph -> O = ( J qTop F ) )
  assume imasval.d: |- ( ph -> D = ( x e. B , y e. B |-> inf ( U_ n e. NN ran ( g e. { h e. ( ( V X. V ) ^m ( 1 ... n ) ) | ( ( F ` ( 1st ` ( h ` 1 ) ) ) = x /\ ( F ` ( 2nd ` ( h ` n ) ) ) = y /\ A. i e. ( 1 ... ( n - 1 ) ) ( F ` ( 2nd ` ( h ` i ) ) ) = ( F ` ( 1st ` ( h ` ( i + 1 ) ) ) ) ) } |-> ( RR*s gsum ( E o. g ) ) ) , RR* , < ) ) )
  assume imasval.l: |- ( ph -> .<_ = ( ( F o. N ) o. `' F ) )
  assume imasval.f: |- ( ph -> F : V -onto-> B )
  assume imasval.r: |- ( ph -> R e. Z )

  disjoint g h
  disjoint g i
  disjoint g n
  disjoint g p
  disjoint g q
  disjoint g x
  disjoint g y
  disjoint F g
  disjoint h i
  disjoint h n
  disjoint h p
  disjoint h q
  disjoint h x
  disjoint h y
  disjoint F h
  disjoint i n
  disjoint i p
  disjoint i q
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint n p
  disjoint n q
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint F p
  disjoint q x
  disjoint q y
  disjoint F q
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint R g
  disjoint R h
  disjoint R i
  disjoint R n
  disjoint R p
  disjoint R q
  disjoint R x
  disjoint R y
  disjoint V h
  disjoint V p
  disjoint V q
  disjoint g ph
  disjoint h ph
  disjoint i ph
  disjoint n ph
  disjoint p ph
  disjoint ph q
  disjoint ph x
  disjoint ph y
  disjoint f r
  disjoint f v
  disjoint .<_ f
  disjoint r v
  disjoint .<_ r
  disjoint .<_ v
  disjoint B f
  disjoint B r
  disjoint B v
  disjoint D f
  disjoint D r
  disjoint D v
  disjoint G f
  disjoint G r
  disjoint G v
  disjoint O f
  disjoint O r
  disjoint O v
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f n
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint g r
  disjoint g v
  disjoint h r
  disjoint h v
  disjoint i r
  disjoint i v
  disjoint n r
  disjoint n v
  disjoint p r
  disjoint p v
  disjoint q r
  disjoint q v
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint v x
  disjoint v y
  disjoint F v
  disjoint R f
  disjoint R r
  disjoint R v
  disjoint I f
  disjoint I r
  disjoint I v
  disjoint .+b f
  disjoint .+b r
  disjoint .+b v
  disjoint f ph
  disjoint ph r
  disjoint ph v
  disjoint .(x) f
  disjoint .(x) r
  disjoint .(x) v
  disjoint .xb f
  disjoint .xb r
  disjoint .xb v
  assert |- ( ph -> U = ( ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+b >. , <. ( .r ` ndx ) , .xb >. } u. { <. ( Scalar ` ndx ) , G >. , <. ( .s ` ndx ) , .(x) >. , <. ( .i ` ndx ) , I >. } ) u. { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , .<_ >. , <. ( dist ` ndx ) , D >. } ) )

  proof
    wph
    cU
    cF
    cR
    cimas
    co
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pb
    cop
    #
    cnx
    cmulr
    cfv
    #
    c.xb
    cop
    #
    ctp
    #
    cnx
    csca
    cfv
    #
    cG
    cop
    #
    cnx
    cvsca
    cfv
    #
    c.xo
    cop
    #
    cnx
    cip
    cfv
    #
    cI
    cop
    #
    ctp
    #
    cun
    #
    cnx
    cts
    cfv
    #
    cO
    cop
    #
    cnx
    cple
    cfv
    #
    c.le
    cop
    #
    cnx
    cds
    cfv
    #
    cD
    cop
    #
    ctp
    #
    cun
    #
    imasval.u
    wph
    vf
    vr
    cF
    cR
    cvv
    cvv
    vv
    vr
    cv
    #
    cbs
    cfv
    #
    @0
    vf
    cv
    #
    crn
    #
    cop
    #
    @2
    vp
    vv
    cv
    #
    vq
    @28
    vp
    cv
    #
    @25
    cfv
    #
    vq
    cv
    #
    @25
    cfv
    #
    cop
    #
    @29
    @31
    @23
    cplusg
    cfv
    #
    co
    #
    @25
    cfv
    #
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    cop
    #
    @4
    vp
    @28
    vq
    @28
    @33
    @29
    @31
    @23
    cmulr
    cfv
    #
    co
    #
    @25
    cfv
    #
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    cop
    #
    ctp
    #
    @7
    @23
    csca
    cfv
    #
    cop
    #
    @9
    vq
    @28
    vp
    vx
    @51
    cbs
    cfv
    #
    @32
    csn
    #
    @29
    @31
    @23
    cvsca
    cfv
    #
    co
    #
    @25
    cfv
    #
    cmpt2
    #
    ciun
    #
    cop
    #
    @11
    vp
    @28
    vq
    @28
    @33
    @29
    @31
    @23
    cip
    cfv
    #
    co
    #
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    cop
    #
    ctp
    #
    cun
    #
    @15
    @23
    ctopn
    cfv
    #
    @25
    cqtop
    co
    #
    cop
    #
    @17
    @25
    @23
    cple
    cfv
    #
    ccom
    #
    @25
    ccnv
    #
    ccom
    #
    cop
    #
    @19
    vx
    vy
    @26
    @26
    vn
    cn
    vg
    c1
    vh
    cv
    #
    cfv
    c1st
    cfv
    #
    @25
    cfv
    #
    vx
    cv
    #
    wceq
    #
    vn
    cv
    #
    @78
    cfv
    c2nd
    cfv
    #
    @25
    cfv
    #
    vy
    cv
    #
    wceq
    #
    vi
    cv
    #
    @78
    cfv
    c2nd
    cfv
    #
    @25
    cfv
    #
    @88
    c1
    caddc
    co
    @78
    cfv
    c1st
    cfv
    #
    @25
    cfv
    #
    wceq
    #
    vi
    c1
    @83
    c1
    cmin
    co
    cfz
    co
    #
    wral
    #
    w3a
    #
    vh
    @28
    @28
    cxp
    #
    c1
    @83
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    cxrs
    @23
    cds
    cfv
    #
    vg
    cv
    #
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    ciun
    #
    cxr
    clt
    cinf
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    cun
    #
    csb
    #
    @22
    cimas
    cvv
    cimas
    vf
    vr
    cvv
    cvv
    @113
    cmpt2
    wceq
    wph
    vx
    vy
    vv
    vf
    vg
    vh
    vi
    vn
    vr
    vq
    vp
    df-imas
    a1i
    wph
    @25
    cF
    wceq
    #
    @23
    cR
    wceq
    #
    wa
    #
    wa
    #
    vv
    @24
    @112
    @22
    cvv
    @117
    @23
    cbs
    fvexd
    @117
    @28
    @24
    wceq
    #
    wa
    #
    @69
    @14
    @111
    @21
    @119
    @50
    @6
    @68
    @13
    @119
    @27
    @1
    @41
    @3
    @49
    @5
    @119
    @26
    cB
    @0
    @119
    @26
    cF
    crn
    #
    cB
    @119
    @25
    cF
    wph
    @114
    @115
    @118
    simplrl
    #
    rneqd
    wph
    @120
    cB
    wceq
    #
    @116
    @118
    wph
    cV
    cB
    cF
    wfo
    #
    @122
    imasval.f
    cV
    cB
    cF
    forn
    syl
    ad2antrr
    eqtrd
    #
    opeq2d
    @119
    @40
    c.pb
    @2
    @119
    @40
    vp
    cV
    vq
    cV
    @29
    cF
    cfv
    #
    @31
    cF
    cfv
    #
    cop
    #
    @29
    @31
    c.pl
    co
    #
    cF
    cfv
    #
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    c.pb
    @119
    vp
    @28
    cV
    @39
    @132
    @119
    @24
    cR
    cbs
    cfv
    #
    @28
    cV
    @119
    @23
    cR
    cbs
    wph
    @114
    @115
    @118
    simplrr
    #
    fveq2d
    @117
    @118
    simpr
    wph
    cV
    @134
    wceq
    @116
    @118
    imasval.v
    ad2antrr
    3eqtr4d
    #
    @119
    vq
    @28
    cV
    @38
    @131
    @136
    @119
    @37
    @130
    @119
    @33
    @127
    @36
    @129
    @119
    @30
    @125
    @32
    @126
    @119
    @29
    @25
    cF
    @121
    fveq1d
    @119
    @31
    @25
    cF
    @121
    fveq1d
    #
    opeq12d
    #
    @119
    @35
    @128
    @25
    cF
    @121
    @119
    @34
    c.pl
    @29
    @31
    @119
    @34
    cR
    cplusg
    cfv
    c.pl
    @119
    @23
    cR
    cplusg
    @135
    fveq2d
    imasval.p
    syl6eqr
    oveqd
    fveq12d
    opeq12d
    sneqd
    iuneq12d
    iuneq12d
    wph
    c.pb
    @133
    wceq
    @116
    @118
    imasval.a
    ad2antrr
    eqtr4d
    opeq2d
    @119
    @48
    c.xb
    @4
    @119
    @48
    vp
    cV
    vq
    cV
    @127
    @29
    @31
    c.xp
    co
    #
    cF
    cfv
    #
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    c.xb
    @119
    vp
    @28
    cV
    @47
    @143
    @136
    @119
    vq
    @28
    cV
    @46
    @142
    @136
    @119
    @45
    @141
    @119
    @33
    @127
    @44
    @140
    @138
    @119
    @43
    @139
    @25
    cF
    @121
    @119
    @42
    c.xp
    @29
    @31
    @119
    @42
    cR
    cmulr
    cfv
    c.xp
    @119
    @23
    cR
    cmulr
    @135
    fveq2d
    imasval.m
    syl6eqr
    oveqd
    fveq12d
    opeq12d
    sneqd
    iuneq12d
    iuneq12d
    wph
    c.xb
    @144
    wceq
    @116
    @118
    imasval.t
    ad2antrr
    eqtr4d
    opeq2d
    tpeq123d
    @119
    @52
    @8
    @60
    @10
    @67
    @12
    @119
    @51
    cG
    @7
    @119
    @51
    cR
    csca
    cfv
    cG
    @119
    @23
    cR
    csca
    @135
    fveq2d
    imasval.g
    syl6eqr
    #
    opeq2d
    @119
    @59
    c.xo
    @9
    @119
    vq
    cV
    @58
    ciun
    vq
    cV
    vp
    vx
    cK
    @126
    csn
    #
    @29
    @31
    c.x
    co
    #
    cF
    cfv
    #
    cmpt2
    #
    ciun
    #
    @59
    c.xo
    @119
    vq
    cV
    @58
    @149
    @119
    vp
    vx
    @53
    @54
    @57
    cK
    @146
    @148
    @119
    @53
    cG
    cbs
    cfv
    cK
    @119
    @51
    cG
    cbs
    @145
    fveq2d
    imasval.k
    syl6eqr
    @119
    @32
    @126
    @137
    sneqd
    @119
    @56
    @147
    @25
    cF
    @121
    @119
    @55
    c.x
    @29
    @31
    @119
    @55
    cR
    cvsca
    cfv
    c.x
    @119
    @23
    cR
    cvsca
    @135
    fveq2d
    imasval.q
    syl6eqr
    oveqd
    fveq12d
    mpt2eq123dv
    iuneq2d
    @119
    vq
    @28
    cV
    @58
    @136
    iuneq1d
    wph
    c.xo
    @150
    wceq
    @116
    @118
    imasval.s
    ad2antrr
    3eqtr4d
    opeq2d
    @119
    @66
    cI
    @11
    @119
    @66
    vp
    cV
    vq
    cV
    @127
    @29
    @31
    c.xi
    co
    #
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    cI
    @119
    vp
    @28
    cV
    @65
    @154
    @136
    @119
    vq
    @28
    cV
    @64
    @153
    @136
    @119
    @63
    @152
    @119
    @33
    @127
    @62
    @151
    @138
    @119
    @61
    c.xi
    @29
    @31
    @119
    @61
    cR
    cip
    cfv
    c.xi
    @119
    @23
    cR
    cip
    @135
    fveq2d
    imasval.i
    syl6eqr
    oveqd
    opeq12d
    sneqd
    iuneq12d
    iuneq12d
    wph
    cI
    @155
    wceq
    @116
    @118
    imasval.w
    ad2antrr
    eqtr4d
    opeq2d
    tpeq123d
    uneq12d
    @119
    @72
    @16
    @77
    @18
    @110
    @20
    @119
    @71
    cO
    @15
    @119
    @71
    cJ
    cF
    cqtop
    co
    #
    cO
    @119
    @70
    cJ
    @25
    cF
    cqtop
    @119
    @70
    cR
    ctopn
    cfv
    cJ
    @119
    @23
    cR
    ctopn
    @135
    fveq2d
    imasval.j
    syl6eqr
    @121
    oveq12d
    wph
    cO
    @156
    wceq
    @116
    @118
    imasval.o
    ad2antrr
    eqtr4d
    opeq2d
    @119
    @76
    c.le
    @17
    @119
    @76
    cF
    cN
    ccom
    #
    cF
    ccnv
    #
    ccom
    #
    c.le
    @119
    @74
    @157
    @75
    @158
    @119
    @25
    cF
    @73
    cN
    @121
    @119
    @73
    cR
    cple
    cfv
    cN
    @119
    @23
    cR
    cple
    @135
    fveq2d
    imasval.n
    syl6eqr
    coeq12d
    @119
    @25
    cF
    @121
    cnveqd
    coeq12d
    wph
    c.le
    @159
    wceq
    @116
    @118
    imasval.l
    ad2antrr
    eqtr4d
    opeq2d
    @119
    @109
    cD
    @19
    @119
    @109
    vx
    vy
    cB
    cB
    vn
    cn
    vg
    @79
    cF
    cfv
    #
    @81
    wceq
    #
    @84
    cF
    cfv
    #
    @86
    wceq
    #
    @89
    cF
    cfv
    #
    @91
    cF
    cfv
    #
    wceq
    #
    vi
    @94
    wral
    #
    w3a
    #
    vh
    cV
    cV
    cxp
    #
    @98
    cmap
    co
    #
    crab
    #
    cxrs
    cE
    @102
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    ciun
    #
    cxr
    clt
    cinf
    #
    cmpt2
    #
    cD
    @119
    vx
    vy
    @26
    @26
    @108
    cB
    cB
    @177
    @124
    @124
    @119
    cxr
    @107
    @176
    clt
    @119
    vn
    cn
    @106
    @175
    @119
    @105
    @174
    @119
    vg
    @100
    @104
    @171
    @173
    @119
    @96
    @168
    vh
    @99
    @170
    @119
    @97
    @169
    @98
    cmap
    @119
    @28
    cV
    @136
    sqxpeqd
    oveq1d
    @119
    @82
    @161
    @87
    @163
    @95
    @167
    @119
    @80
    @160
    @81
    @119
    @79
    @25
    cF
    @121
    fveq1d
    eqeq1d
    @119
    @85
    @162
    @86
    @119
    @84
    @25
    cF
    @121
    fveq1d
    eqeq1d
    @119
    @93
    @166
    vi
    @94
    @119
    @90
    @164
    @92
    @165
    @119
    @89
    @25
    cF
    @121
    fveq1d
    @119
    @91
    @25
    cF
    @121
    fveq1d
    eqeq12d
    ralbidv
    3anbi123d
    rabeqbidv
    @119
    @103
    @172
    cxrs
    cgsu
    @119
    @101
    cE
    @102
    @119
    @101
    cR
    cds
    cfv
    cE
    @119
    @23
    cR
    cds
    @135
    fveq2d
    imasval.e
    syl6eqr
    coeq1d
    oveq2d
    mpteq12dv
    rneqd
    iuneq2d
    infeq1d
    mpt2eq123dv
    wph
    cD
    @178
    wceq
    @116
    @118
    imasval.d
    ad2antrr
    eqtr4d
    opeq2d
    tpeq123d
    uneq12d
    csbied
    wph
    cV
    cB
    cF
    wf
    #
    cV
    cvv
    wcel
    cF
    cvv
    wcel
    wph
    @123
    @179
    imasval.f
    cV
    cB
    cF
    fof
    syl
    wph
    cV
    @134
    cvv
    imasval.v
    cR
    cbs
    fvex
    syl6eqel
    cV
    cB
    cvv
    cF
    fex
    syl2anc
    wph
    cR
    cZ
    wcel
    cR
    cvv
    wcel
    imasval.r
    cR
    cZ
    elex
    syl
    @22
    cvv
    wcel
    wph
    @14
    @21
    @6
    @13
    @1
    @3
    @5
    tpex
    @8
    @10
    @12
    tpex
    unex
    @16
    @18
    @20
    tpex
    unex
    a1i
    ovmpt2d
    eqtrd
end
