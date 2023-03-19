include "cmin.mm"
include "co.mm"
include "cicc.mm"
include "cv.mm"
include "cfv.mm"
include "citg.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "caddc.mm"
include "cc.mm"
include "oveq2i.mm"
include "recnd.mm"
include "rpred.mm"
include "subadd4b.mm"
include "syl5eq.mm"
include "subidd.mm"
include "oveq1d.mm"
include "resubcld.mm"
include "addid2d.mm"
include "3eqtrd.mm"
include "pncan3d.mm"
include "oveq12d.mm"
include "eqcomd.mm"
include "itgeq1d.mm"
include "cfzo.mm"
include "cmpt.mm"
include "cif.mm"
include "cfz.mm"
include "cn.mm"
include "c1.mm"
include "wral.mm"
include "cr.mm"
include "cmap.mm"
include "crab.mm"
include "wcel.mm"
include "wb.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "a1i.mm"
include "anbi2d.mm"
include "rabbidv.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "wiso.mm"
include "ltsubrpd.mm"
include "fourierdlem54.mm"
include "simpld.mm"
include "syl5eqel.mm"
include "simprd.mm"
include "adantr.mm"
include "simpr.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "syldan.mm"
include "cbvmptv.mm"
include "eqid.mm"
include "cioo.mm"
include "cres.mm"
include "wf.mm"
include "adantlr.mm"
include "ccncf.mm"
include "cpnf.mm"
include "rexrd.mm"
include "cxr.mm"
include "pnfxr.mm"
include "ltpnfd.mm"
include "eliood.mm"
include "fourierdlem90.mm"
include "climc.mm"
include "fourierdlem89.mm"
include "fourierdlem91.mm"
include "fourierdlem92.mm"
include "eqtrd.mm"
include "ffvelrnd.mm"
include "fourierdlem105.mm"
include "itgcl.mm"
include "eqeltrrd.mm"
include "cle.mm"
include "fourierdlem11.mm"
include "simp3d.mm"
include "ltled.mm"
include "lesub1d.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "ltsub23d.mm"
include "eliccd.mm"
include "cibl.mm"
include "ltsub1dd.mm"
include "itgspliticc.mm"
include "addsubassd.mm"
include "oveq2d.mm"
include "subid1d.mm"
include "subcld.mm"
include "subsub4d.mm"
include "cneg.mm"
include "df-neg.mm"
include "negsubdi2d.mm"
include "syl5eqr.mm"
include "3eqtr3d.mm"
include "addid1d.mm"
include "iccssred.mm"
include "feqresmpt.mm"
include "fssresd.mm"
include "ioossicc.mm"
include "fourierdlem15.mm"
include "fourierdlem8.mm"
include "syl5ss.mm"
include "resabs1d.mm"
include "eqeltrd.mm"
include "eleqtrd.mm"
include "fourierdlem69.mm"
include "addsub12d.mm"
include "syl6eqr.mm"
include "negsubd.mm"
include "subsubd.mm"
include "id.mm"
include "syl6breq.mm"
include "adantl.mm"
include "lesubd.mm"
include "wss.mm"
include "leidd.mm"
include "rpge0d.mm"
include "subge02d.mm"
include "iccss.mm"
include "syl22anc.mm"
include "cvol.mm"
include "cdm.mm"
include "iccmbl.mm"
include "syl2anc.mm"
include "iblss.mm"
include "3eqtrrd.mm"
include "eqtr4d.mm"
include "pncand.mm"
include "ltlecasei.mm"

theorem fourierdlem107
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
  let vk: setvar k
  let vm: setvar m
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cZ: class Z
  let vp: setvar p
  let vj: setvar j
  assume fourierdlem107.a: |- ( ph -> A e. RR )
  assume fourierdlem107.b: |- ( ph -> B e. RR )
  assume fourierdlem107.t: |- T = ( B - A )
  assume fourierdlem107.x: |- ( ph -> X e. RR+ )
  assume fourierdlem107.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem107.m: |- ( ph -> M e. NN )
  assume fourierdlem107.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem107.f: |- ( ph -> F : RR --> CC )
  assume fourierdlem107.fper: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem107.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem107.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )
  assume fourierdlem107.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )
  assume fourierdlem107.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( A - X ) /\ ( p ` m ) = A ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem107.h: |- H = ( { ( A - X ) , A } u. { y e. ( ( A - X ) [,] A ) | E. k e. ZZ ( y + ( k x. T ) ) e. ran Q } )
  assume fourierdlem107.n: |- N = ( ( # ` H ) - 1 )
  assume fourierdlem107.s: |- S = ( iota f f Isom < , < ( ( 0 ... N ) , H ) )
  assume fourierdlem107.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )
  assume fourierdlem107.z: |- Z = ( y e. ( A (,] B ) |-> if ( y = B , A , y ) )
  assume fourierdlem107.i: |- I = ( x e. RR |-> sup ( { i e. ( 0 ..^ M ) | ( Q ` i ) <_ ( Z ` ( E ` x ) ) } , RR , < ) )

  disjoint A f
  disjoint A k
  disjoint A y
  disjoint f k
  disjoint f y
  disjoint k y
  disjoint A i
  disjoint A x
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint k x
  disjoint x y
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint B f
  disjoint B k
  disjoint B y
  disjoint B i
  disjoint B x
  disjoint B m
  disjoint B p
  disjoint E f
  disjoint E k
  disjoint E y
  disjoint E i
  disjoint E x
  disjoint F i
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
  disjoint L x
  disjoint L y
  disjoint M i
  disjoint M x
  disjoint M y
  disjoint M m
  disjoint M p
  disjoint N f
  disjoint N k
  disjoint N y
  disjoint N i
  disjoint N x
  disjoint N m
  disjoint N p
  disjoint Q f
  disjoint Q k
  disjoint Q y
  disjoint Q i
  disjoint Q x
  disjoint Q m
  disjoint Q p
  disjoint R x
  disjoint R y
  disjoint S f
  disjoint S k
  disjoint S y
  disjoint S i
  disjoint S x
  disjoint S p
  disjoint T f
  disjoint T k
  disjoint T y
  disjoint T i
  disjoint T x
  disjoint T m
  disjoint T p
  disjoint X f
  disjoint X y
  disjoint X i
  disjoint X m
  disjoint X p
  disjoint X x
  disjoint Z i
  disjoint Z x
  disjoint Z y
  disjoint f ph
  disjoint k ph
  disjoint ph y
  disjoint i ph
  disjoint ph x
  disjoint k x
  disjoint A j
  disjoint f j
  disjoint j k
  disjoint j y
  disjoint i j
  disjoint j x
  disjoint j m
  disjoint j p
  disjoint F j
  disjoint N j
  disjoint S j
  disjoint T j
  disjoint X j
  disjoint j ph
  assert |- ( ph -> S. ( ( A - X ) [,] ( B - X ) ) ( F ` x ) _d x = S. ( A [,] B ) ( F ` x ) _d x )

  proof
    wph
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
    @4
    citg
    #
    wceq
    cT
    cX
    wph
    cT
    cX
    clt
    wbr
    #
    wa
    #
    @5
    vx
    @0
    cA
    cicc
    co
    #
    @4
    citg
    #
    vx
    @1
    cA
    cicc
    co
    #
    @4
    citg
    #
    cmin
    co
    #
    @11
    vx
    @1
    cB
    cicc
    co
    #
    @4
    citg
    #
    @7
    cmin
    co
    #
    cmin
    co
    #
    @7
    @9
    @5
    cc0
    cmin
    co
    @5
    @5
    @13
    @11
    cmin
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    @5
    @14
    @9
    cc0
    @20
    @5
    cmin
    @9
    cc0
    @11
    @11
    cmin
    co
    #
    @5
    @13
    caddc
    co
    #
    @11
    cmin
    co
    @20
    wph
    cc0
    @22
    wceq
    @8
    wph
    @22
    cc0
    wph
    @11
    wph
    @16
    @11
    cc
    wph
    @16
    vx
    @0
    cT
    caddc
    co
    #
    cA
    cT
    caddc
    co
    #
    cicc
    co
    #
    @4
    citg
    @11
    wph
    vx
    @15
    @26
    @4
    wph
    @26
    @15
    wph
    @24
    @1
    @25
    cB
    cicc
    wph
    @24
    cA
    cA
    cmin
    co
    #
    @1
    caddc
    co
    #
    cc0
    @1
    caddc
    co
    @1
    wph
    @24
    @0
    cB
    cA
    cmin
    co
    #
    caddc
    co
    @28
    cT
    @29
    @0
    caddc
    fourierdlem107.t
    oveq2i
    wph
    cA
    cX
    cB
    cA
    wph
    cA
    fourierdlem107.a
    recnd
    #
    wph
    cX
    wph
    cX
    fourierdlem107.x
    rpred
    #
    recnd
    wph
    cB
    fourierdlem107.b
    recnd
    #
    @30
    subadd4b
    syl5eq
    wph
    @27
    cc0
    @1
    caddc
    wph
    cA
    @30
    subidd
    oveq1d
    wph
    @1
    wph
    @1
    wph
    cB
    cX
    fourierdlem107.b
    @31
    resubcld
    #
    recnd
    addid2d
    3eqtrd
    wph
    @25
    cA
    @29
    caddc
    co
    cB
    cT
    @29
    cA
    caddc
    fourierdlem107.t
    oveq2i
    wph
    cA
    cB
    @30
    @32
    pncan3d
    syl5eq
    oveq12d
    eqcomd
    itgeq1d
    wph
    vx
    @0
    cA
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
    cZ
    cfv
    #
    @35
    cI
    cfv
    #
    cQ
    cfv
    wceq
    @37
    vi
    cc0
    cM
    cfzo
    co
    #
    cR
    cmpt
    #
    cfv
    @36
    cF
    cfv
    cif
    vi
    cc0
    cN
    cfz
    co
    #
    vi
    cv
    #
    cS
    cfv
    #
    cT
    caddc
    co
    #
    cmpt
    cT
    vj
    vm
    cF
    vm
    cn
    cc0
    vp
    cv
    #
    cfv
    #
    @24
    wceq
    vm
    cv
    #
    @44
    cfv
    #
    @25
    wceq
    wa
    @34
    @44
    cfv
    #
    @34
    c1
    caddc
    co
    #
    @44
    cfv
    #
    clt
    wbr
    #
    vj
    cc0
    @46
    cfzo
    co
    #
    wral
    #
    wa
    vp
    cr
    cc0
    @46
    cfz
    co
    cmap
    co
    #
    crab
    cmpt
    #
    @49
    cS
    cfv
    #
    cE
    cfv
    #
    @37
    c1
    caddc
    co
    cQ
    cfv
    wceq
    @37
    vi
    @38
    cL
    cmpt
    #
    cfv
    @57
    cF
    cfv
    cif
    cN
    vp
    wph
    cA
    cX
    fourierdlem107.a
    @31
    resubcld
    #
    fourierdlem107.a
    cO
    vm
    cn
    @45
    @0
    wceq
    @47
    cA
    wceq
    wa
    #
    @41
    @44
    cfv
    #
    @41
    c1
    caddc
    co
    #
    @44
    cfv
    #
    clt
    wbr
    #
    vi
    @52
    wral
    #
    wa
    #
    vp
    @54
    crab
    #
    cmpt
    vm
    cn
    @60
    @53
    wa
    #
    vp
    @54
    crab
    #
    cmpt
    fourierdlem107.o
    vm
    cn
    @67
    @69
    @46
    cn
    wcel
    #
    @66
    @68
    vp
    @54
    @70
    @65
    @53
    @60
    @65
    @53
    wb
    @70
    @64
    @51
    vi
    vj
    @52
    @41
    @34
    wceq
    #
    @61
    @48
    @63
    @50
    clt
    @41
    @34
    @44
    fveq2
    @71
    @62
    @49
    @44
    @41
    @34
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    cbvralv
    a1i
    anbi2d
    rabbidv
    mpteq2ia
    eqtri
    wph
    cN
    cn
    wcel
    #
    cS
    cN
    cO
    cfv
    wcel
    #
    wph
    @72
    @73
    wa
    @40
    cH
    clt
    clt
    cS
    wiso
    wph
    vy
    cA
    cB
    @0
    cA
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
    fourierdlem107.t
    fourierdlem107.p
    fourierdlem107.m
    fourierdlem107.q
    @59
    fourierdlem107.a
    wph
    cA
    cX
    fourierdlem107.a
    fourierdlem107.x
    ltsubrpd
    #
    fourierdlem107.o
    fourierdlem107.h
    fourierdlem107.n
    fourierdlem107.s
    fourierdlem54
    simpld
    #
    simpld
    wph
    cT
    @29
    cr
    fourierdlem107.t
    wph
    cB
    cA
    fourierdlem107.b
    fourierdlem107.a
    resubcld
    syl5eqel
    #
    wph
    @72
    @73
    @75
    simprd
    wph
    @3
    @10
    wcel
    #
    @3
    cr
    wcel
    #
    @3
    cT
    caddc
    co
    cF
    cfv
    @4
    wceq
    #
    wph
    @77
    wa
    #
    @0
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @77
    @78
    wph
    @81
    @77
    @59
    adantr
    wph
    @82
    @77
    fourierdlem107.a
    adantr
    wph
    @77
    simpr
    @0
    cA
    @3
    eliccre
    syl3anc
    #
    fourierdlem107.fper
    syldan
    vi
    vj
    @40
    @43
    @35
    cT
    caddc
    co
    @71
    @42
    @35
    cT
    caddc
    @41
    @34
    cS
    fveq2
    oveq1d
    cbvmptv
    @55
    eqid
    fourierdlem107.f
    wph
    @34
    cc0
    cN
    cfzo
    co
    wcel
    #
    wa
    #
    vx
    vy
    cA
    cB
    @0
    cA
    cP
    cQ
    vy
    @36
    @56
    @57
    cmin
    co
    #
    caddc
    co
    @57
    @86
    caddc
    co
    cioo
    co
    vy
    cv
    @86
    cmin
    co
    cF
    @36
    @57
    cioo
    co
    cres
    #
    cfv
    cmpt
    #
    cS
    cT
    @86
    vf
    vi
    vk
    vm
    cE
    cF
    @87
    cH
    cI
    @34
    cZ
    cM
    cN
    cO
    vp
    fourierdlem107.p
    fourierdlem107.t
    wph
    cM
    cn
    wcel
    #
    @84
    fourierdlem107.m
    adantr
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @84
    fourierdlem107.q
    adantr
    #
    wph
    cr
    cc
    cF
    wf
    #
    @84
    fourierdlem107.f
    adantr
    #
    wph
    @78
    @79
    @84
    fourierdlem107.fper
    adantlr
    #
    wph
    @41
    @38
    wcel
    #
    cF
    @41
    cQ
    cfv
    #
    @62
    cQ
    cfv
    #
    cioo
    co
    #
    cres
    #
    @99
    cc
    ccncf
    co
    #
    wcel
    #
    @84
    fourierdlem107.fcn
    adantlr
    #
    wph
    @81
    @84
    @59
    adantr
    #
    @85
    @0
    cpnf
    cA
    @85
    @0
    @104
    rexrd
    cpnf
    cxr
    wcel
    #
    @85
    pnfxr
    a1i
    wph
    @82
    @84
    fourierdlem107.a
    adantr
    wph
    @0
    cA
    clt
    wbr
    @84
    @74
    adantr
    wph
    cA
    cpnf
    clt
    wbr
    @84
    wph
    cA
    fourierdlem107.a
    ltpnfd
    #
    adantr
    eliood
    #
    fourierdlem107.o
    fourierdlem107.h
    fourierdlem107.n
    fourierdlem107.s
    fourierdlem107.e
    fourierdlem107.z
    wph
    @84
    simpr
    #
    @86
    eqid
    #
    @87
    eqid
    @88
    eqid
    fourierdlem107.i
    fourierdlem90
    @85
    vx
    vy
    cA
    cB
    @0
    cA
    cP
    cQ
    cR
    cS
    cT
    @86
    vf
    vi
    vk
    vm
    cE
    cF
    cH
    cI
    @34
    cM
    cN
    cO
    @39
    cZ
    vp
    fourierdlem107.p
    fourierdlem107.t
    @90
    @92
    @94
    @95
    @103
    wph
    @96
    cR
    @100
    @97
    climc
    co
    #
    wcel
    #
    @84
    fourierdlem107.r
    adantlr
    @104
    @107
    fourierdlem107.o
    fourierdlem107.h
    fourierdlem107.n
    fourierdlem107.s
    fourierdlem107.e
    fourierdlem107.z
    @108
    @109
    fourierdlem107.i
    @39
    eqid
    fourierdlem89
    @85
    vx
    vy
    cA
    cB
    @0
    cA
    cP
    cQ
    cS
    cT
    @86
    vf
    vi
    vk
    vm
    cE
    cF
    cH
    cI
    @34
    cL
    cM
    cN
    cO
    @58
    cZ
    vp
    fourierdlem107.p
    fourierdlem107.t
    @90
    @92
    @94
    @95
    @103
    wph
    @96
    cL
    @100
    @98
    climc
    co
    #
    wcel
    #
    @84
    fourierdlem107.l
    adantlr
    @104
    @107
    fourierdlem107.o
    fourierdlem107.h
    fourierdlem107.n
    fourierdlem107.s
    fourierdlem107.e
    fourierdlem107.z
    @108
    @109
    fourierdlem107.i
    @58
    eqid
    fourierdlem91
    fourierdlem92
    eqtrd
    #
    wph
    vx
    @15
    @4
    cc
    wph
    @3
    @15
    wcel
    #
    wa
    #
    cr
    cc
    @3
    cF
    wph
    @93
    @115
    fourierdlem107.f
    adantr
    @116
    @1
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @115
    @78
    wph
    @117
    @115
    @33
    adantr
    wph
    @118
    @115
    fourierdlem107.b
    adantr
    wph
    @115
    simpr
    @1
    cB
    @3
    eliccre
    syl3anc
    ffvelrnd
    #
    wph
    vx
    cA
    cB
    @1
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
    vp
    fourierdlem107.p
    fourierdlem107.t
    fourierdlem107.m
    fourierdlem107.q
    fourierdlem107.f
    fourierdlem107.fper
    fourierdlem107.fcn
    fourierdlem107.r
    fourierdlem107.l
    @33
    wph
    @1
    cpnf
    cB
    wph
    @1
    @33
    rexrd
    #
    @105
    wph
    pnfxr
    a1i
    #
    fourierdlem107.b
    wph
    cB
    cX
    fourierdlem107.b
    fourierdlem107.x
    ltsubrpd
    wph
    cB
    fourierdlem107.b
    ltpnfd
    eliood
    fourierdlem105
    itgcl
    #
    eqeltrrd
    #
    subidd
    #
    eqcomd
    adantr
    @9
    @11
    @23
    @11
    cmin
    @9
    vx
    @0
    @1
    cA
    @4
    cc
    wph
    @81
    @8
    @59
    adantr
    #
    wph
    @82
    @8
    fourierdlem107.a
    adantr
    #
    @9
    @0
    cA
    @1
    @125
    @126
    wph
    @117
    @8
    @33
    adantr
    #
    @9
    cA
    cB
    cle
    wbr
    #
    @0
    @1
    cle
    wbr
    #
    wph
    @128
    @8
    wph
    cA
    cB
    fourierdlem107.a
    fourierdlem107.b
    wph
    @82
    @118
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
    fourierdlem107.p
    fourierdlem107.m
    fourierdlem107.q
    fourierdlem11
    simp3d
    #
    ltled
    adantr
    #
    wph
    @128
    @129
    wb
    @8
    wph
    cA
    cB
    cX
    fourierdlem107.a
    fourierdlem107.b
    @31
    lesub1d
    adantr
    mpbid
    @9
    @1
    cA
    @127
    @126
    @9
    cB
    cA
    cX
    wph
    @118
    @8
    fourierdlem107.b
    adantr
    #
    @126
    wph
    cX
    cr
    wcel
    #
    @8
    @31
    adantr
    @9
    @29
    cT
    cX
    clt
    fourierdlem107.t
    wph
    @8
    simpr
    syl5eqbrr
    ltsub23d
    #
    ltled
    #
    eliccd
    wph
    @77
    @4
    cc
    wcel
    #
    @8
    @80
    cr
    cc
    @3
    cF
    wph
    @93
    @77
    fourierdlem107.f
    adantr
    @83
    ffvelrnd
    adantlr
    wph
    vx
    @2
    @4
    cmpt
    cibl
    wcel
    @8
    wph
    vx
    cA
    cB
    @0
    @1
    cP
    cQ
    cR
    cT
    vi
    vm
    cF
    cL
    cM
    vp
    fourierdlem107.p
    fourierdlem107.t
    fourierdlem107.m
    fourierdlem107.q
    fourierdlem107.f
    fourierdlem107.fper
    fourierdlem107.fcn
    fourierdlem107.r
    fourierdlem107.l
    @59
    wph
    @0
    cpnf
    @1
    wph
    @0
    @59
    rexrd
    #
    @121
    @33
    wph
    cA
    cB
    cX
    fourierdlem107.a
    fourierdlem107.b
    @31
    @130
    ltsub1dd
    wph
    @1
    @33
    ltpnfd
    eliood
    fourierdlem105
    #
    adantr
    @9
    vx
    cA
    cB
    @1
    cA
    cP
    cQ
    cR
    cT
    vi
    vm
    cF
    cL
    cM
    vp
    fourierdlem107.p
    fourierdlem107.t
    wph
    @89
    @8
    fourierdlem107.m
    adantr
    wph
    @91
    @8
    fourierdlem107.q
    adantr
    wph
    @93
    @8
    fourierdlem107.f
    adantr
    wph
    @78
    @79
    @8
    fourierdlem107.fper
    adantlr
    wph
    @96
    @102
    @8
    fourierdlem107.fcn
    adantlr
    wph
    @96
    @111
    @8
    fourierdlem107.r
    adantlr
    wph
    @96
    @113
    @8
    fourierdlem107.l
    adantlr
    @127
    @9
    @1
    cpnf
    cA
    wph
    @1
    cxr
    wcel
    @8
    @120
    adantr
    @105
    @9
    pnfxr
    a1i
    @126
    @134
    @9
    cA
    @126
    ltpnfd
    eliood
    fourierdlem105
    #
    itgspliticc
    oveq1d
    @9
    @5
    @13
    @11
    wph
    @5
    cc
    wcel
    @8
    wph
    vx
    @2
    @4
    cc
    wph
    @3
    @2
    wcel
    #
    wa
    #
    cr
    cc
    @3
    cF
    wph
    @93
    @140
    fourierdlem107.f
    adantr
    @141
    @81
    @117
    @140
    @78
    wph
    @81
    @140
    @59
    adantr
    wph
    @117
    @140
    @33
    adantr
    wph
    @140
    simpr
    @0
    @1
    @3
    eliccre
    syl3anc
    ffvelrnd
    #
    @138
    itgcl
    #
    adantr
    #
    @9
    vx
    @12
    @4
    cc
    wph
    @3
    @12
    wcel
    #
    @136
    @8
    wph
    @145
    wa
    #
    cr
    cc
    @3
    cF
    wph
    @93
    @145
    fourierdlem107.f
    adantr
    @146
    @117
    @82
    @145
    @78
    wph
    @117
    @145
    @33
    adantr
    wph
    @82
    @145
    fourierdlem107.a
    adantr
    wph
    @145
    simpr
    @1
    cA
    @3
    eliccre
    syl3anc
    ffvelrnd
    adantlr
    @139
    itgcl
    #
    wph
    @11
    cc
    wcel
    @8
    @123
    adantr
    #
    addsubassd
    3eqtrd
    oveq2d
    @9
    @5
    @144
    subid1d
    @9
    @5
    @5
    cmin
    co
    #
    @19
    cmin
    co
    #
    cc0
    @19
    cmin
    co
    #
    @21
    @14
    wph
    @150
    @151
    wceq
    @8
    wph
    @149
    cc0
    @19
    cmin
    wph
    @5
    @143
    subidd
    oveq1d
    adantr
    @9
    @5
    @5
    @19
    @144
    @144
    @9
    @13
    @11
    @147
    @148
    subcld
    subsub4d
    @9
    @151
    @19
    cneg
    @14
    @19
    df-neg
    @9
    @13
    @11
    @147
    @148
    negsubdi2d
    syl5eqr
    3eqtr3d
    3eqtr3d
    @9
    @13
    @17
    @11
    cmin
    @9
    @13
    cc0
    caddc
    co
    #
    @13
    @16
    @16
    cmin
    co
    #
    caddc
    co
    #
    @13
    @17
    wph
    @152
    @154
    wceq
    @8
    wph
    cc0
    @153
    @13
    caddc
    wph
    @153
    cc0
    wph
    @16
    @122
    subidd
    #
    eqcomd
    oveq2d
    adantr
    @9
    @13
    @147
    addid1d
    @9
    @154
    @13
    @16
    @13
    @7
    caddc
    co
    #
    cmin
    co
    #
    caddc
    co
    @16
    @13
    @156
    cmin
    co
    #
    caddc
    co
    #
    @17
    @9
    @153
    @157
    @13
    caddc
    @9
    @16
    @156
    @16
    cmin
    @9
    vx
    @1
    cA
    cB
    @4
    cc
    @127
    @132
    @9
    @1
    cB
    cA
    @127
    @132
    @126
    @135
    @131
    eliccd
    wph
    @115
    @136
    @8
    @119
    adantlr
    @139
    wph
    vx
    @6
    @4
    cmpt
    #
    cibl
    wcel
    #
    @8
    wph
    cF
    @6
    cres
    #
    @160
    cibl
    wph
    vx
    cr
    cc
    @6
    cF
    fourierdlem107.f
    wph
    cA
    cB
    fourierdlem107.a
    fourierdlem107.b
    iccssred
    #
    feqresmpt
    wph
    cA
    cB
    cP
    cQ
    cR
    vi
    vm
    @162
    cL
    cM
    vp
    fourierdlem107.p
    fourierdlem107.m
    fourierdlem107.q
    wph
    cr
    cc
    @6
    cF
    fourierdlem107.f
    @163
    fssresd
    wph
    @96
    wa
    #
    @162
    @99
    cres
    #
    @100
    @101
    @164
    cF
    @99
    @6
    @164
    @99
    @97
    @98
    cicc
    co
    @6
    @97
    @98
    ioossicc
    @164
    cA
    cB
    cQ
    @41
    cM
    wph
    cA
    cxr
    wcel
    @96
    wph
    cA
    fourierdlem107.a
    rexrd
    adantr
    wph
    cB
    cxr
    wcel
    @96
    wph
    cB
    fourierdlem107.b
    rexrd
    adantr
    wph
    cc0
    cM
    cfz
    co
    @6
    cQ
    wf
    @96
    wph
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem107.p
    fourierdlem107.m
    fourierdlem107.q
    fourierdlem15
    adantr
    wph
    @96
    simpr
    fourierdlem8
    syl5ss
    resabs1d
    #
    fourierdlem107.fcn
    eqeltrd
    @164
    cR
    @110
    @165
    @97
    climc
    co
    fourierdlem107.r
    @164
    @100
    @165
    @97
    climc
    @164
    @165
    @100
    @166
    eqcomd
    #
    oveq1d
    eleqtrd
    @164
    cL
    @112
    @165
    @98
    climc
    co
    fourierdlem107.l
    @164
    @100
    @165
    @98
    climc
    @167
    oveq1d
    eleqtrd
    fourierdlem69
    eqeltrrd
    #
    adantr
    itgspliticc
    #
    oveq2d
    oveq2d
    @9
    @13
    @16
    @156
    @147
    wph
    @16
    cc
    wcel
    #
    @8
    @122
    adantr
    #
    @9
    @16
    @156
    cc
    @169
    @171
    eqeltrrd
    addsub12d
    @9
    @159
    @16
    @13
    @13
    cmin
    co
    #
    @7
    cmin
    co
    #
    caddc
    co
    @16
    @7
    cneg
    #
    caddc
    co
    @17
    @9
    @158
    @173
    @16
    caddc
    @9
    @173
    @158
    @9
    @13
    @13
    @7
    @147
    @147
    wph
    @7
    cc
    wcel
    @8
    wph
    vx
    @6
    @4
    cc
    wph
    @3
    @6
    wcel
    #
    wa
    #
    cr
    cc
    @3
    cF
    wph
    @93
    @175
    fourierdlem107.f
    adantr
    @176
    @82
    @118
    @175
    @78
    wph
    @82
    @175
    fourierdlem107.a
    adantr
    wph
    @118
    @175
    fourierdlem107.b
    adantr
    wph
    @175
    simpr
    cA
    cB
    @3
    eliccre
    syl3anc
    ffvelrnd
    #
    @168
    itgcl
    #
    adantr
    #
    subsub4d
    eqcomd
    oveq2d
    @9
    @173
    @174
    @16
    caddc
    @9
    @173
    cc0
    @7
    cmin
    co
    @174
    @9
    @172
    cc0
    @7
    cmin
    @9
    @13
    @147
    subidd
    oveq1d
    @7
    df-neg
    syl6eqr
    oveq2d
    @9
    @16
    @7
    @171
    @179
    negsubd
    3eqtrd
    3eqtrd
    3eqtr3d
    oveq2d
    wph
    @18
    @7
    wceq
    @8
    wph
    @18
    @11
    @16
    cmin
    co
    #
    @7
    caddc
    co
    cc0
    @7
    caddc
    co
    @7
    wph
    @11
    @16
    @7
    @123
    @122
    @178
    subsubd
    wph
    @180
    cc0
    @7
    caddc
    wph
    @180
    @22
    cc0
    wph
    @16
    @11
    @11
    cmin
    @114
    oveq2d
    @124
    eqtrd
    oveq1d
    wph
    @7
    @178
    addid2d
    3eqtrd
    adantr
    3eqtrd
    wph
    cX
    cT
    cle
    wbr
    #
    wa
    #
    @5
    @7
    @11
    caddc
    co
    #
    @16
    cmin
    co
    #
    @183
    @11
    cmin
    co
    @7
    @182
    @5
    @11
    vx
    cA
    @1
    cicc
    co
    #
    @4
    citg
    #
    caddc
    co
    @11
    @7
    @16
    cmin
    co
    #
    caddc
    co
    #
    @184
    @182
    vx
    @0
    cA
    @1
    @4
    cc
    wph
    @81
    @181
    @59
    adantr
    #
    wph
    @117
    @181
    @33
    adantr
    #
    @182
    @0
    @1
    cA
    @189
    @190
    wph
    @82
    @181
    fourierdlem107.a
    adantr
    #
    wph
    @0
    cA
    cle
    wbr
    @181
    wph
    @0
    cA
    @59
    fourierdlem107.a
    @74
    ltled
    adantr
    @182
    cX
    cB
    cA
    wph
    @133
    @181
    @31
    adantr
    wph
    @118
    @181
    fourierdlem107.b
    adantr
    #
    @191
    @181
    cX
    @29
    cle
    wbr
    wph
    @181
    cX
    cT
    @29
    cle
    @181
    id
    fourierdlem107.t
    syl6breq
    adantl
    lesubd
    #
    eliccd
    wph
    @140
    @136
    @181
    @142
    adantlr
    wph
    vx
    @10
    @4
    cmpt
    cibl
    wcel
    @181
    wph
    vx
    cA
    cB
    @0
    cA
    cP
    cQ
    cR
    cT
    vi
    vm
    cF
    cL
    cM
    vp
    fourierdlem107.p
    fourierdlem107.t
    fourierdlem107.m
    fourierdlem107.q
    fourierdlem107.f
    fourierdlem107.fper
    fourierdlem107.fcn
    fourierdlem107.r
    fourierdlem107.l
    @59
    wph
    @0
    cpnf
    cA
    @137
    @121
    fourierdlem107.a
    @74
    @106
    eliood
    fourierdlem105
    adantr
    wph
    vx
    @185
    @4
    cmpt
    cibl
    wcel
    @181
    wph
    vx
    @185
    @6
    @4
    cc
    wph
    @82
    @118
    cA
    cA
    cle
    wbr
    @1
    cB
    cle
    wbr
    #
    @185
    @6
    wss
    fourierdlem107.a
    fourierdlem107.b
    wph
    cA
    fourierdlem107.a
    leidd
    wph
    cc0
    cX
    cle
    wbr
    #
    @194
    wph
    cX
    fourierdlem107.x
    rpge0d
    #
    wph
    cB
    cX
    fourierdlem107.b
    @31
    subge02d
    #
    mpbid
    cA
    cB
    cA
    @1
    iccss
    syl22anc
    wph
    @82
    @117
    @185
    cvol
    cdm
    #
    wcel
    fourierdlem107.a
    @33
    cA
    @1
    iccmbl
    syl2anc
    @177
    @168
    iblss
    #
    adantr
    #
    itgspliticc
    @182
    @186
    @187
    @11
    caddc
    @182
    @187
    @186
    @16
    caddc
    co
    #
    @16
    cmin
    co
    #
    @186
    @153
    caddc
    co
    #
    @186
    @182
    @7
    @201
    @16
    cmin
    @182
    vx
    cA
    @1
    cB
    @4
    cc
    @191
    @192
    @182
    cA
    cB
    @1
    @191
    @192
    @190
    @193
    @182
    @195
    @194
    wph
    @195
    @181
    @196
    adantr
    wph
    @195
    @194
    wb
    @181
    @197
    adantr
    mpbid
    eliccd
    wph
    @175
    @136
    @181
    @177
    adantlr
    #
    @200
    @182
    vx
    @15
    @6
    @4
    cc
    @182
    @82
    @118
    cA
    @1
    cle
    wbr
    cB
    cB
    cle
    wbr
    #
    @15
    @6
    wss
    @191
    @192
    @193
    wph
    @205
    @181
    wph
    cB
    fourierdlem107.b
    leidd
    adantr
    cA
    cB
    @1
    cB
    iccss
    syl22anc
    wph
    @15
    @198
    wcel
    #
    @181
    wph
    @117
    @118
    @206
    @33
    fourierdlem107.b
    @1
    cB
    iccmbl
    syl2anc
    adantr
    @204
    wph
    @161
    @181
    @168
    adantr
    #
    iblss
    itgspliticc
    oveq1d
    wph
    @202
    @203
    wceq
    @181
    wph
    @186
    @16
    @16
    wph
    vx
    @185
    @4
    cc
    wph
    @3
    @185
    wcel
    #
    wa
    #
    cr
    cc
    @3
    cF
    wph
    @93
    @208
    fourierdlem107.f
    adantr
    @209
    @82
    @117
    @208
    @78
    wph
    @82
    @208
    fourierdlem107.a
    adantr
    wph
    @117
    @208
    @33
    adantr
    wph
    @208
    simpr
    cA
    @1
    @3
    eliccre
    syl3anc
    ffvelrnd
    @199
    itgcl
    #
    @122
    @122
    addsubassd
    adantr
    wph
    @203
    @186
    wceq
    @181
    wph
    @203
    @186
    cc0
    caddc
    co
    @186
    wph
    @153
    cc0
    @186
    caddc
    @155
    oveq2d
    wph
    @186
    @210
    addid1d
    eqtrd
    adantr
    3eqtrrd
    oveq2d
    @182
    @188
    @7
    @180
    caddc
    co
    @184
    @182
    @11
    @7
    @16
    @182
    @16
    @11
    cc
    wph
    @16
    @11
    wceq
    @181
    @114
    adantr
    #
    wph
    @170
    @181
    @122
    adantr
    #
    eqeltrrd
    #
    @182
    vx
    @6
    @4
    cc
    @204
    @207
    itgcl
    #
    @212
    addsub12d
    @182
    @7
    @11
    @16
    @214
    @213
    @212
    addsubassd
    eqtr4d
    3eqtrd
    @182
    @16
    @11
    @183
    cmin
    @211
    oveq2d
    @182
    @7
    @11
    @214
    @213
    pncand
    3eqtrd
    @76
    @31
    ltlecasei
end
