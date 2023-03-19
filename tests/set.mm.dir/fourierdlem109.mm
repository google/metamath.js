include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cicc.mm"
include "cv.mm"
include "cfv.mm"
include "citg.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "elrpd.mm"
include "cn.mm"
include "cc.mm"
include "wf.mm"
include "caddc.mm"
include "adantlr.mm"
include "cfzo.mm"
include "c1.mm"
include "cioo.mm"
include "cres.mm"
include "ccncf.mm"
include "climc.mm"
include "fourierdlem108.mm"
include "wn.mm"
include "oveq2.mm"
include "recnd.mm"
include "subid1d.mm"
include "sylan9eqr.mm"
include "oveq12d.mm"
include "itgeq1d.mm"
include "simpll.mm"
include "syl.mm"
include "0red.mm"
include "neqned.mm"
include "simplr.mm"
include "lttri5d.mm"
include "cneg.mm"
include "subcld.mm"
include "subnegd.mm"
include "npcand.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "cmpt.mm"
include "cif.mm"
include "resubcld.mm"
include "eqid.mm"
include "renegcld.mm"
include "lt0neg1d.mm"
include "biimpa.mm"
include "wral.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "wb.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "a1i.mm"
include "rabbiia.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "wiso.mm"
include "fourierdlem11.mm"
include "simp3d.mm"
include "ltsub1dd.mm"
include "fourierdlem54.mm"
include "simpld.mm"
include "simprd.mm"
include "nnncan2d.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "cpnf.mm"
include "rexrd.mm"
include "cxr.mm"
include "pnfxr.mm"
include "ltpnfd.mm"
include "eliood.mm"
include "cpr.mm"
include "cmul.mm"
include "crn.mm"
include "cz.mm"
include "wrex.mm"
include "cun.mm"
include "eleq1d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "uneq2i.mm"
include "cle.mm"
include "csup.mm"
include "breq1d.mm"
include "supeq1i.mm"
include "fourierdlem90.mm"
include "fourierdlem89.mm"
include "fourierdlem91.mm"
include "eqtr2d.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"

theorem fourierdlem109
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let vp: setvar p
  assume fourierdlem109.a: |- ( ph -> A e. RR )
  assume fourierdlem109.b: |- ( ph -> B e. RR )
  assume fourierdlem109.t: |- T = ( B - A )
  assume fourierdlem109.x: |- ( ph -> X e. RR )
  assume fourierdlem109.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem109.m: |- ( ph -> M e. NN )
  assume fourierdlem109.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem109.f: |- ( ph -> F : RR --> CC )
  assume fourierdlem109.fper: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem109.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem109.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )
  assume fourierdlem109.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )
  assume fourierdlem109.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( A - X ) /\ ( p ` m ) = ( B - X ) ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem109.h: |- H = ( { ( A - X ) , ( B - X ) } u. { x e. ( ( A - X ) [,] ( B - X ) ) | E. k e. ZZ ( x + ( k x. T ) ) e. ran Q } )
  assume fourierdlem109.n: |- N = ( ( # ` H ) - 1 )
  assume fourierdlem109.16: |- S = ( iota f f Isom < , < ( ( 0 ... N ) , H ) )
  assume fourierdlem109.17: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )
  assume fourierdlem109.18: |- J = ( y e. ( A (,] B ) |-> if ( y = B , A , y ) )
  assume fourierdlem109.19: |- I = ( x e. RR |-> sup ( { j e. ( 0 ..^ M ) | ( Q ` j ) <_ ( J ` ( E ` x ) ) } , RR , < ) )

  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A y
  disjoint f j
  disjoint f k
  disjoint f y
  disjoint j k
  disjoint j y
  disjoint k y
  disjoint A i
  disjoint A x
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint k x
  disjoint x y
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint j m
  disjoint j p
  disjoint m p
  disjoint B f
  disjoint B j
  disjoint B k
  disjoint B y
  disjoint B i
  disjoint B x
  disjoint B m
  disjoint B p
  disjoint E f
  disjoint E j
  disjoint E k
  disjoint E y
  disjoint E i
  disjoint E x
  disjoint F i
  disjoint F j
  disjoint F x
  disjoint F y
  disjoint H f
  disjoint H y
  disjoint H x
  disjoint I f
  disjoint I k
  disjoint I y
  disjoint I i
  disjoint I x
  disjoint J i
  disjoint J j
  disjoint J x
  disjoint J y
  disjoint L x
  disjoint L y
  disjoint M i
  disjoint M x
  disjoint M y
  disjoint M j
  disjoint M m
  disjoint M p
  disjoint N f
  disjoint N j
  disjoint N k
  disjoint N y
  disjoint N i
  disjoint N x
  disjoint N m
  disjoint N p
  disjoint Q f
  disjoint Q j
  disjoint Q k
  disjoint Q y
  disjoint Q i
  disjoint Q x
  disjoint Q m
  disjoint Q p
  disjoint R x
  disjoint R y
  disjoint S f
  disjoint S j
  disjoint S k
  disjoint S y
  disjoint S i
  disjoint S x
  disjoint S m
  disjoint S p
  disjoint T f
  disjoint T j
  disjoint T k
  disjoint T y
  disjoint T i
  disjoint T x
  disjoint T m
  disjoint T p
  disjoint X f
  disjoint X j
  disjoint X y
  disjoint X i
  disjoint X m
  disjoint X p
  disjoint X x
  disjoint f ph
  disjoint j ph
  disjoint k ph
  disjoint ph y
  disjoint i ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> S. ( ( A - X ) [,] ( B - X ) ) ( F ` x ) _d x = S. ( A [,] B ) ( F ` x ) _d x )

  proof
    wph
    cc0
    cX
    clt
    wbr
    #
    vx
    cA
    cX
    cmin
    co
    #
    cB
    cX
    cmin
    co
    #
    cicc
    co
    #
    vx
    cv
    #
    cF
    cfv
    #
    citg
    #
    vx
    cA
    cB
    cicc
    co
    #
    @5
    citg
    #
    wceq
    #
    wph
    @0
    wa
    #
    vx
    cA
    cB
    cP
    cQ
    cR
    cT
    vi
    vm
    cF
    cL
    cM
    cX
    vp
    wph
    cA
    cr
    wcel
    #
    @0
    fourierdlem109.a
    adantr
    wph
    cB
    cr
    wcel
    #
    @0
    fourierdlem109.b
    adantr
    fourierdlem109.t
    @10
    cX
    wph
    cX
    cr
    wcel
    #
    @0
    fourierdlem109.x
    adantr
    wph
    @0
    simpr
    elrpd
    fourierdlem109.p
    wph
    cM
    cn
    wcel
    #
    @0
    fourierdlem109.m
    adantr
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @0
    fourierdlem109.q
    adantr
    wph
    cr
    cc
    cF
    wf
    #
    @0
    fourierdlem109.f
    adantr
    wph
    @4
    cr
    wcel
    #
    @4
    cT
    caddc
    co
    #
    cF
    cfv
    #
    @5
    wceq
    #
    @0
    fourierdlem109.fper
    adantlr
    wph
    vi
    cv
    #
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    cF
    @21
    cQ
    cfv
    #
    @21
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    cres
    #
    @27
    cc
    ccncf
    co
    wcel
    #
    @0
    fourierdlem109.fcn
    adantlr
    wph
    @23
    cR
    @28
    @24
    climc
    co
    wcel
    #
    @0
    fourierdlem109.r
    adantlr
    wph
    @23
    cL
    @28
    @26
    climc
    co
    wcel
    #
    @0
    fourierdlem109.l
    adantlr
    fourierdlem108
    wph
    @0
    wn
    #
    wa
    #
    cX
    cc0
    wceq
    #
    @9
    wph
    @34
    @9
    @32
    wph
    @34
    wa
    #
    vx
    @3
    @7
    @5
    @35
    @1
    cA
    @2
    cB
    cicc
    @34
    wph
    @1
    cA
    cc0
    cmin
    co
    cA
    cX
    cc0
    cA
    cmin
    oveq2
    wph
    cA
    wph
    cA
    fourierdlem109.a
    recnd
    #
    subid1d
    sylan9eqr
    @34
    wph
    @2
    cB
    cc0
    cmin
    co
    cB
    cX
    cc0
    cB
    cmin
    oveq2
    wph
    cB
    wph
    cB
    fourierdlem109.b
    recnd
    #
    subid1d
    sylan9eqr
    oveq12d
    itgeq1d
    adantlr
    @33
    @34
    wn
    #
    wa
    #
    wph
    cX
    cc0
    clt
    wbr
    #
    @9
    wph
    @32
    @38
    simpll
    #
    @39
    cX
    cc0
    @39
    wph
    @13
    @41
    fourierdlem109.x
    syl
    @39
    0red
    @39
    cX
    cc0
    @33
    @38
    simpr
    neqned
    wph
    @32
    @38
    simplr
    lttri5d
    wph
    @40
    wa
    #
    @8
    vx
    @1
    cX
    cneg
    #
    cmin
    co
    #
    @2
    @43
    cmin
    co
    #
    cicc
    co
    #
    @5
    citg
    #
    @6
    wph
    @8
    @47
    wceq
    @40
    wph
    vx
    @7
    @46
    @5
    wph
    @46
    @7
    wph
    @44
    cA
    @45
    cB
    cicc
    wph
    @44
    @1
    cX
    caddc
    co
    cA
    wph
    @1
    cX
    wph
    cA
    cX
    @36
    wph
    cX
    fourierdlem109.x
    recnd
    #
    subcld
    @48
    subnegd
    wph
    cA
    cX
    @36
    @48
    npcand
    eqtrd
    wph
    @45
    @2
    cX
    caddc
    co
    cB
    wph
    @2
    cX
    wph
    cB
    cX
    @37
    @48
    subcld
    @48
    subnegd
    wph
    cB
    cX
    @37
    @48
    npcand
    eqtrd
    oveq12d
    eqcomd
    itgeq1d
    adantr
    @42
    vx
    @1
    @2
    cO
    cS
    vj
    cv
    #
    cS
    cfv
    #
    cE
    cfv
    cJ
    cfv
    #
    @50
    cI
    cfv
    #
    cQ
    cfv
    wceq
    @52
    vi
    @22
    cR
    cmpt
    #
    cfv
    @51
    cF
    cfv
    cif
    #
    @2
    @1
    cmin
    co
    #
    vj
    vm
    cF
    @49
    c1
    caddc
    co
    #
    cS
    cfv
    #
    cE
    cfv
    #
    @52
    c1
    caddc
    co
    cQ
    cfv
    wceq
    @52
    vi
    @22
    cL
    cmpt
    #
    cfv
    @58
    cF
    cfv
    cif
    #
    cN
    @43
    vp
    wph
    @1
    cr
    wcel
    #
    @40
    wph
    cA
    cX
    fourierdlem109.a
    fourierdlem109.x
    resubcld
    #
    adantr
    wph
    @2
    cr
    wcel
    @40
    wph
    cB
    cX
    fourierdlem109.b
    fourierdlem109.x
    resubcld
    #
    adantr
    @55
    eqid
    @42
    @43
    wph
    @43
    cr
    wcel
    @40
    wph
    cX
    fourierdlem109.x
    renegcld
    adantr
    wph
    @40
    cc0
    @43
    clt
    wbr
    wph
    cX
    fourierdlem109.x
    lt0neg1d
    biimpa
    elrpd
    cO
    vm
    cn
    cc0
    vp
    cv
    #
    cfv
    @1
    wceq
    vm
    cv
    #
    @64
    cfv
    @2
    wceq
    wa
    #
    @21
    @64
    cfv
    #
    @25
    @64
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    @65
    cfzo
    co
    #
    wral
    #
    wa
    #
    vp
    cr
    cc0
    @65
    cfz
    co
    cmap
    co
    #
    crab
    #
    cmpt
    vm
    cn
    @66
    @49
    @64
    cfv
    #
    @56
    @64
    cfv
    #
    clt
    wbr
    #
    vj
    @70
    wral
    #
    wa
    #
    vp
    @73
    crab
    #
    cmpt
    fourierdlem109.o
    vm
    cn
    @74
    @80
    @72
    @79
    vp
    @73
    @72
    @79
    wb
    @64
    @73
    wcel
    @71
    @78
    @66
    @69
    @77
    vi
    vj
    @70
    @21
    @49
    wceq
    #
    @67
    @75
    @68
    @76
    clt
    @21
    @49
    @64
    fveq2
    @81
    @25
    @56
    @64
    @21
    @49
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    cbvralv
    anbi2i
    a1i
    rabbiia
    mpteq2i
    eqtri
    wph
    cN
    cn
    wcel
    #
    @40
    wph
    @82
    cS
    cN
    cO
    cfv
    wcel
    #
    wph
    @82
    @83
    wa
    cc0
    cN
    cfz
    co
    cH
    clt
    clt
    cS
    wiso
    wph
    vx
    cA
    cB
    @1
    @2
    cP
    cQ
    cS
    cT
    vf
    vi
    vk
    vm
    cH
    cM
    cN
    cO
    vp
    fourierdlem109.t
    fourierdlem109.p
    fourierdlem109.m
    fourierdlem109.q
    @62
    @63
    wph
    cA
    cB
    cX
    fourierdlem109.a
    fourierdlem109.b
    fourierdlem109.x
    wph
    @11
    @12
    cA
    cB
    clt
    wbr
    wph
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem109.p
    fourierdlem109.m
    fourierdlem109.q
    fourierdlem11
    simp3d
    ltsub1dd
    #
    fourierdlem109.o
    fourierdlem109.h
    fourierdlem109.n
    fourierdlem109.16
    fourierdlem54
    simpld
    #
    simpld
    adantr
    wph
    @83
    @40
    wph
    @82
    @83
    @85
    simprd
    adantr
    wph
    @16
    @40
    fourierdlem109.f
    adantr
    wph
    @17
    @4
    @55
    caddc
    co
    #
    cF
    cfv
    #
    @5
    wceq
    @40
    wph
    @17
    wa
    #
    @87
    @19
    @5
    @88
    @86
    @18
    cF
    wph
    @86
    @18
    wceq
    @17
    wph
    @55
    cT
    @4
    caddc
    wph
    @55
    cB
    cA
    cmin
    co
    cT
    wph
    cB
    cA
    cX
    @37
    @36
    @48
    nnncan2d
    fourierdlem109.t
    syl6eqr
    oveq2d
    adantr
    fveq2d
    fourierdlem109.fper
    eqtrd
    adantlr
    wph
    @49
    cc0
    cN
    cfzo
    co
    wcel
    #
    cF
    @50
    @57
    cioo
    co
    #
    cres
    #
    @90
    cc
    ccncf
    co
    wcel
    @40
    wph
    @89
    wa
    #
    vx
    vy
    cA
    cB
    @1
    @2
    cP
    cQ
    vy
    @51
    @57
    @58
    cmin
    co
    #
    caddc
    co
    @58
    @93
    caddc
    co
    cioo
    co
    vy
    cv
    #
    @93
    cmin
    co
    cF
    @51
    @58
    cioo
    co
    cres
    #
    cfv
    cmpt
    #
    cS
    cT
    @93
    vf
    vi
    vk
    vm
    cE
    cF
    @95
    cH
    cI
    @49
    cJ
    cM
    cN
    cO
    vp
    fourierdlem109.p
    fourierdlem109.t
    wph
    @14
    @89
    fourierdlem109.m
    adantr
    #
    wph
    @15
    @89
    fourierdlem109.q
    adantr
    #
    wph
    @16
    @89
    fourierdlem109.f
    adantr
    #
    wph
    @17
    @20
    @89
    fourierdlem109.fper
    adantlr
    #
    wph
    @23
    @29
    @89
    fourierdlem109.fcn
    adantlr
    #
    wph
    @61
    @89
    @62
    adantr
    #
    wph
    @2
    @1
    cpnf
    cioo
    co
    wcel
    @89
    wph
    @1
    cpnf
    @2
    wph
    @1
    @62
    rexrd
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    @63
    @84
    wph
    @2
    @63
    ltpnfd
    eliood
    adantr
    #
    fourierdlem109.o
    cH
    @1
    @2
    cpr
    #
    @4
    vk
    cv
    cT
    cmul
    co
    #
    caddc
    co
    #
    cQ
    crn
    #
    wcel
    #
    vk
    cz
    wrex
    #
    vx
    @3
    crab
    #
    cun
    @104
    @94
    @105
    caddc
    co
    #
    @107
    wcel
    #
    vk
    cz
    wrex
    #
    vy
    @3
    crab
    #
    cun
    fourierdlem109.h
    @110
    @114
    @104
    @109
    @113
    vx
    vy
    @3
    @4
    @94
    wceq
    #
    @108
    @112
    vk
    cz
    @115
    @106
    @111
    @107
    @4
    @94
    @105
    caddc
    oveq1
    eleq1d
    rexbidv
    cbvrabv
    uneq2i
    eqtri
    #
    fourierdlem109.n
    fourierdlem109.16
    fourierdlem109.17
    fourierdlem109.18
    wph
    @89
    simpr
    #
    @93
    eqid
    #
    @95
    eqid
    @96
    eqid
    cI
    vx
    cr
    @49
    cQ
    cfv
    #
    @4
    cE
    cfv
    cJ
    cfv
    #
    cle
    wbr
    #
    vj
    @22
    crab
    #
    cr
    clt
    csup
    #
    cmpt
    vx
    cr
    @24
    @120
    cle
    wbr
    #
    vi
    @22
    crab
    #
    cr
    clt
    csup
    #
    cmpt
    fourierdlem109.19
    vx
    cr
    @123
    @126
    cr
    @122
    @125
    clt
    @121
    @124
    vj
    vi
    @22
    @49
    @21
    wceq
    @119
    @24
    @120
    cle
    @49
    @21
    cQ
    fveq2
    breq1d
    cbvrabv
    supeq1i
    mpteq2i
    eqtri
    #
    fourierdlem90
    adantlr
    wph
    @89
    @54
    @91
    @50
    climc
    co
    wcel
    @40
    @92
    vx
    vy
    cA
    cB
    @1
    @2
    cP
    cQ
    cR
    cS
    cT
    @93
    vf
    vi
    vk
    vm
    cE
    cF
    cH
    cI
    @49
    cM
    cN
    cO
    @53
    cJ
    vp
    fourierdlem109.p
    fourierdlem109.t
    @97
    @98
    @99
    @100
    @101
    wph
    @23
    @30
    @89
    fourierdlem109.r
    adantlr
    @102
    @103
    fourierdlem109.o
    @116
    fourierdlem109.n
    fourierdlem109.16
    fourierdlem109.17
    fourierdlem109.18
    @117
    @118
    @127
    @53
    eqid
    fourierdlem89
    adantlr
    wph
    @89
    @60
    @91
    @57
    climc
    co
    wcel
    @40
    @92
    vx
    vy
    cA
    cB
    @1
    @2
    cP
    cQ
    cS
    cT
    @93
    vf
    vi
    vk
    vm
    cE
    cF
    cH
    cI
    @49
    cL
    cM
    cN
    cO
    @59
    cJ
    vp
    fourierdlem109.p
    fourierdlem109.t
    @97
    @98
    @99
    @100
    @101
    wph
    @23
    @31
    @89
    fourierdlem109.l
    adantlr
    @102
    @103
    fourierdlem109.o
    @116
    fourierdlem109.n
    fourierdlem109.16
    fourierdlem109.17
    fourierdlem109.18
    @117
    @118
    @127
    @59
    eqid
    fourierdlem91
    adantlr
    fourierdlem108
    eqtr2d
    syl2anc
    pm2.61dan
    pm2.61dan
end
