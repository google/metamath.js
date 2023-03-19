include "cfunc.mm"
include "co.mm"
include "cxp.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cxpc.mm"
include "cinv.mm"
include "cnat.mm"
include "eqid.mm"
include "fucbas.mm"
include "oppcbas.mm"
include "xpcbas.mm"
include "wcel.mm"
include "yonedalem1.mm"
include "simpld.mm"
include "simprd.mm"
include "yonedalem3.mm"
include "c1st.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wceq.mm"
include "wf.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "ccat.mm"
include "adantr.mm"
include "chomf.mm"
include "crn.mm"
include "wss.mm"
include "cun.mm"
include "simprl.mm"
include "simprr.mm"
include "yonedalem3a.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "yonedalem4c.mm"
include "fmptd.mm"
include "wfn.mm"
include "chom.mm"
include "c2nd.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fnmpti.mm"
include "weq.mm"
include "simpl.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "simplr.mm"
include "oveq2d.mm"
include "simpll.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "fveq1d.mm"
include "mpteq12dv.mm"
include "mpteq2dva.mm"
include "ovmpt2a.mm"
include "adantl.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "dffn5.mm"
include "sylib.mm"
include "oppccat.mm"
include "syl.mm"
include "unssbd.mm"
include "ssexd.mm"
include "setccat.mm"
include "evlf1.mm"
include "yonedalem21.mm"
include "feq123d.mm"
include "mpbird.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "fvexd.mm"
include "fmpt2d.mm"
include "ffvelrnda.mm"
include "fveq1.mm"
include "fvmpt.mm"
include "catidcl.mm"
include "yonedalem4b.mm"
include "ccid.mm"
include "wrel.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcid.mm"
include "oppcid.mm"
include "ad2antrr.mm"
include "funcf1.mm"
include "setcbas.mm"
include "feq3d.mm"
include "ffvelrnd.mm"
include "setcid.mm"
include "3eqtr3d.mm"
include "fvresi.mm"
include "3eqtrd.mm"
include "syldan.mm"
include "mptresid.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "mpbid.mm"
include "nat1st2nd.mm"
include "natfn.mm"
include "yon11.mm"
include "cop.mm"
include "cco.mm"
include "oppchom.mm"
include "syl6eleqr.mm"
include "nati.mm"
include "yoncl.mm"
include "funcf2.mm"
include "elsetchom.mm"
include "natcl.mm"
include "setcco.mm"
include "eleqtrrd.mm"
include "fvco3.mm"
include "yon12.mm"
include "catlid.mm"
include "eqtr3d.mm"
include "feqmptd.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"
include "fcof1o.mm"
include "syl22anc.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "fovrnda.mm"
include "setcinv.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "breq123d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "invfuc.mm"
include "fnmpt2i.mm"
include "mpbi.mm"
include "syl6breqr.mm"

theorem yonedainv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.1: class .1.
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cH: class H
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vh: setvar h
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vv: setvar v
  let cF: class F
  let cK: class K
  let cG: class G
  let cP: class P
  let cX: class X
  assume yoneda.y: |- Y = ( Yon ` C )
  assume yoneda.b: |- B = ( Base ` C )
  assume yoneda.1: |- .1. = ( Id ` C )
  assume yoneda.o: |- O = ( oppCat ` C )
  assume yoneda.s: |- S = ( SetCat ` U )
  assume yoneda.t: |- T = ( SetCat ` V )
  assume yoneda.q: |- Q = ( O FuncCat S )
  assume yoneda.h: |- H = ( HomF ` Q )
  assume yoneda.r: |- R = ( ( Q Xc. O ) FuncCat T )
  assume yoneda.e: |- E = ( O evalF S )
  assume yoneda.z: |- Z = ( H o.func ( ( <. ( 1st ` Y ) , tpos ( 2nd ` Y ) >. o.func ( Q 2ndF O ) ) pairF ( Q 1stF O ) ) )
  assume yoneda.c: |- ( ph -> C e. Cat )
  assume yoneda.w: |- ( ph -> V e. W )
  assume yoneda.u: |- ( ph -> ran ( Homf ` C ) C_ U )
  assume yoneda.v: |- ( ph -> ( ran ( Homf ` Q ) u. U ) C_ V )
  assume yoneda.m: |- M = ( f e. ( O Func S ) , x e. B |-> ( a e. ( ( ( 1st ` Y ) ` x ) ( O Nat S ) f ) |-> ( ( a ` x ) ` ( .1. ` x ) ) ) )
  assume yonedainv.i: |- I = ( Inv ` R )
  assume yonedainv.n: |- N = ( f e. ( O Func S ) , x e. B |-> ( u e. ( ( 1st ` f ) ` x ) |-> ( y e. B |-> ( g e. ( y ( Hom ` C ) x ) |-> ( ( ( x ( 2nd ` f ) y ) ` g ) ` u ) ) ) ) )

  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint .1. a
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint .1. f
  disjoint g x
  disjoint g y
  disjoint .1. g
  disjoint x y
  disjoint .1. x
  disjoint .1. y
  disjoint a u
  disjoint g u
  disjoint u y
  disjoint C a
  disjoint f u
  disjoint C f
  disjoint C g
  disjoint u x
  disjoint C u
  disjoint C x
  disjoint C y
  disjoint E a
  disjoint E f
  disjoint E g
  disjoint E u
  disjoint E y
  disjoint B a
  disjoint B f
  disjoint B g
  disjoint B u
  disjoint B x
  disjoint B y
  disjoint N a
  disjoint O a
  disjoint O f
  disjoint O g
  disjoint O u
  disjoint O x
  disjoint O y
  disjoint S a
  disjoint S f
  disjoint S g
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint M g
  disjoint M u
  disjoint M y
  disjoint Q a
  disjoint Q f
  disjoint Q g
  disjoint Q u
  disjoint Q x
  disjoint T f
  disjoint T g
  disjoint T u
  disjoint T y
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint R u
  disjoint Y a
  disjoint Y f
  disjoint Y g
  disjoint Y u
  disjoint Y x
  disjoint Y y
  disjoint Z a
  disjoint Z f
  disjoint Z g
  disjoint Z u
  disjoint Z x
  disjoint Z y
  disjoint a b
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint .1. b
  disjoint a h
  disjoint a k
  disjoint a w
  disjoint a z
  disjoint A a
  disjoint b h
  disjoint b k
  disjoint b u
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint g h
  disjoint g k
  disjoint g w
  disjoint g z
  disjoint A g
  disjoint h k
  disjoint h u
  disjoint h w
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint k u
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint f h
  disjoint f w
  disjoint f z
  disjoint h x
  disjoint C h
  disjoint w x
  disjoint C w
  disjoint x z
  disjoint C z
  disjoint a v
  disjoint b v
  disjoint E b
  disjoint f k
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint E h
  disjoint k v
  disjoint E k
  disjoint u v
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint E v
  disjoint E w
  disjoint E z
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint k x
  disjoint F k
  disjoint F u
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint K a
  disjoint K b
  disjoint K y
  disjoint B b
  disjoint B h
  disjoint B k
  disjoint v x
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint G y
  disjoint N b
  disjoint N h
  disjoint N k
  disjoint N v
  disjoint N w
  disjoint N z
  disjoint I z
  disjoint O b
  disjoint O h
  disjoint O k
  disjoint O v
  disjoint O w
  disjoint O z
  disjoint S b
  disjoint S h
  disjoint S k
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint M b
  disjoint M h
  disjoint M k
  disjoint M w
  disjoint M z
  disjoint Q b
  disjoint Q v
  disjoint Q w
  disjoint Q z
  disjoint T h
  disjoint T v
  disjoint T w
  disjoint T z
  disjoint P a
  disjoint P b
  disjoint P f
  disjoint P g
  disjoint P x
  disjoint P y
  disjoint b ph
  disjoint h ph
  disjoint k ph
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint R v
  disjoint R z
  disjoint Y b
  disjoint Y h
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint Z b
  disjoint Z h
  disjoint Z k
  disjoint Z v
  disjoint Z w
  disjoint Z z
  disjoint X a
  disjoint X b
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X k
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> M ( Z I E ) N )

  proof
    wph
    cM
    vz
    cO
    cS
    cfunc
    co
    #
    cB
    cxp
    #
    vz
    cv
    #
    cN
    cfv
    #
    cmpt
    #
    cN
    cZ
    cE
    cI
    co
    wph
    vz
    @1
    cQ
    cO
    cxpc
    co
    #
    cT
    cR
    cM
    cZ
    cE
    cI
    cT
    cinv
    cfv
    #
    @5
    cT
    cnat
    co
    #
    @3
    yoneda.r
    cQ
    cO
    @5
    @0
    cB
    @5
    eqid
    cO
    cS
    cQ
    yoneda.q
    fucbas
    #
    cB
    cC
    cO
    yoneda.o
    yoneda.b
    oppcbas
    #
    xpcbas
    #
    @7
    eqid
    wph
    cZ
    @5
    cT
    cfunc
    co
    #
    wcel
    #
    cE
    @11
    wcel
    #
    wph
    cB
    cC
    cQ
    cR
    cS
    cT
    cU
    c.1
    cE
    cH
    cO
    cV
    cW
    cY
    cZ
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    yoneda.c
    yoneda.w
    yoneda.u
    yoneda.v
    yonedalem1
    #
    simpld
    #
    wph
    @12
    @13
    @14
    simprd
    #
    yonedainv.i
    @6
    eqid
    #
    wph
    vx
    cB
    cC
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    cE
    cH
    cM
    cO
    cV
    cW
    cY
    cZ
    va
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    yoneda.c
    yoneda.w
    yoneda.u
    yoneda.v
    yoneda.m
    yonedalem3
    wph
    @2
    cM
    cfv
    #
    @3
    @2
    cZ
    c1st
    cfv
    #
    cfv
    #
    @2
    cE
    c1st
    cfv
    #
    cfv
    #
    @6
    co
    #
    wbr
    #
    vz
    @1
    wph
    vh
    cv
    #
    vw
    cv
    #
    cM
    co
    #
    @25
    @26
    cN
    co
    #
    @25
    @26
    @19
    co
    #
    @25
    @26
    @21
    co
    #
    @6
    co
    #
    wbr
    #
    vw
    cB
    wral
    vh
    @0
    wral
    @24
    vz
    @1
    wral
    wph
    @32
    vh
    vw
    @0
    cB
    wph
    @25
    @0
    wcel
    #
    @26
    cB
    wcel
    #
    wa
    #
    wa
    #
    @32
    @29
    @30
    @27
    wf1o
    #
    @28
    @27
    ccnv
    #
    wceq
    #
    wa
    #
    @36
    @37
    @38
    @28
    wceq
    #
    wa
    #
    @40
    @36
    @29
    @30
    @27
    wf
    #
    @30
    @29
    @28
    wf
    #
    @27
    @28
    ccom
    #
    cid
    @30
    cres
    #
    wceq
    @28
    @27
    ccom
    #
    cid
    @29
    cres
    #
    wceq
    @42
    @36
    @27
    va
    @26
    cY
    c1st
    cfv
    #
    cfv
    #
    @25
    cO
    cS
    cnat
    co
    #
    co
    #
    @26
    c.1
    cfv
    #
    @26
    va
    cv
    #
    cfv
    #
    cfv
    #
    cmpt
    #
    wceq
    #
    @43
    @36
    vx
    cB
    cC
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    cE
    @25
    cH
    cM
    cO
    cV
    cW
    @26
    cY
    cZ
    va
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    wph
    cC
    ccat
    wcel
    #
    @35
    yoneda.c
    adantr
    #
    wph
    cV
    cW
    wcel
    #
    @35
    yoneda.w
    adantr
    #
    wph
    cC
    chomf
    cfv
    crn
    cU
    wss
    #
    @35
    yoneda.u
    adantr
    #
    wph
    cQ
    chomf
    cfv
    crn
    #
    cU
    cun
    cV
    wss
    #
    @35
    yoneda.v
    adantr
    #
    wph
    @33
    @34
    simprl
    #
    wph
    @33
    @34
    simprr
    #
    yoneda.m
    yonedalem3a
    simprd
    #
    @36
    @44
    @26
    @25
    c1st
    cfv
    #
    cfv
    #
    @52
    vb
    @72
    vb
    cv
    #
    @28
    cfv
    #
    cmpt
    #
    wf
    @36
    vb
    @72
    @74
    @52
    @75
    @36
    @73
    @72
    wcel
    #
    wa
    #
    vx
    vy
    vu
    @73
    cB
    cC
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    vg
    cE
    @25
    cH
    cN
    cO
    cV
    cW
    @26
    cY
    cZ
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    @36
    @59
    @76
    @60
    adantr
    @36
    @61
    @76
    @62
    adantr
    @36
    @63
    @76
    @64
    adantr
    @36
    @66
    @76
    @67
    adantr
    wph
    @33
    @34
    @76
    simplrl
    wph
    @33
    @34
    @76
    simplrr
    yonedainv.n
    @36
    @76
    simpr
    yonedalem4c
    #
    @75
    eqid
    fmptd
    @36
    @30
    @72
    @29
    @52
    @28
    @75
    @36
    @28
    @72
    wfn
    #
    @28
    @75
    wceq
    @36
    @79
    vu
    @72
    vy
    cB
    vg
    vy
    cv
    #
    @26
    cC
    chom
    cfv
    #
    co
    #
    vu
    cv
    #
    vg
    cv
    #
    @26
    @80
    @25
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    cmpt
    #
    @72
    wfn
    vu
    @72
    @90
    @91
    vy
    cB
    @89
    cB
    cC
    cbs
    cfv
    cvv
    yoneda.b
    cC
    cbs
    fvex
    eqeltri
    mptex
    @91
    eqid
    fnmpti
    @36
    @72
    @28
    @91
    @35
    @28
    @91
    wceq
    wph
    vf
    vx
    @25
    @26
    @0
    cB
    vu
    vx
    cv
    #
    vf
    cv
    #
    c1st
    cfv
    #
    cfv
    #
    vy
    cB
    vg
    @80
    @92
    @81
    co
    #
    @83
    @84
    @92
    @80
    @93
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    cmpt
    #
    @91
    cN
    vf
    vh
    weq
    #
    vx
    vw
    weq
    #
    wa
    #
    vu
    @95
    @102
    @72
    @90
    @106
    @92
    @26
    @94
    @71
    @106
    @93
    @25
    c1st
    @104
    @105
    simpl
    fveq2d
    @104
    @105
    simpr
    fveq12d
    @106
    vy
    cB
    @101
    @89
    @106
    @80
    cB
    wcel
    #
    wa
    #
    vg
    @96
    @100
    @82
    @88
    @108
    @92
    @26
    @80
    @81
    @104
    @105
    @107
    simplr
    #
    oveq2d
    @108
    @83
    @99
    @87
    @108
    @84
    @98
    @86
    @108
    @92
    @26
    @80
    @80
    @97
    @85
    @108
    @93
    @25
    c2nd
    @104
    @105
    @107
    simpll
    fveq2d
    @109
    @108
    @80
    eqidd
    oveq123d
    fveq1d
    fveq1d
    mpteq12dv
    mpteq2dva
    mpteq12dv
    yonedainv.n
    vu
    @72
    @90
    @26
    @71
    fvex
    mptex
    ovmpt2a
    adantl
    fneq1d
    mpbiri
    vb
    @72
    @28
    dffn5
    sylib
    #
    @36
    cB
    cO
    cS
    cE
    @25
    @26
    yoneda.e
    wph
    cO
    ccat
    wcel
    #
    @35
    wph
    @59
    @111
    yoneda.c
    cC
    cO
    yoneda.o
    oppccat
    syl
    adantr
    wph
    cS
    ccat
    wcel
    #
    @35
    wph
    cU
    cvv
    wcel
    #
    @112
    wph
    cU
    cV
    cW
    yoneda.w
    wph
    @65
    cU
    cV
    yoneda.v
    unssbd
    ssexd
    #
    cS
    cU
    cvv
    yoneda.s
    setccat
    syl
    adantr
    @9
    @68
    @69
    evlf1
    #
    @36
    cB
    cC
    cQ
    cR
    cS
    cT
    cU
    c.1
    cE
    @25
    cH
    cO
    cV
    cW
    @26
    cY
    cZ
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    @60
    @62
    @64
    @67
    @68
    @69
    yonedalem21
    #
    feq123d
    mpbird
    #
    @36
    @45
    vk
    @30
    vk
    cv
    #
    @28
    cfv
    #
    @27
    cfv
    #
    cmpt
    #
    @46
    @36
    @43
    @44
    @45
    @121
    wceq
    @70
    @117
    vk
    @27
    @28
    @30
    @29
    @30
    fcompt
    syl2anc
    @36
    @121
    vk
    @30
    @118
    cmpt
    @46
    @36
    vk
    @30
    @120
    @118
    @36
    @118
    @30
    wcel
    #
    @118
    @72
    wcel
    #
    @120
    @118
    wceq
    @36
    @122
    @123
    @36
    @30
    @72
    @118
    @115
    eleq2d
    biimpa
    @36
    @123
    wa
    #
    @120
    @119
    @57
    cfv
    #
    @53
    @26
    @119
    cfv
    #
    cfv
    #
    @118
    @124
    @119
    @27
    @57
    @124
    @58
    @43
    @124
    vx
    cB
    cC
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    cE
    @25
    cH
    cM
    cO
    cV
    cW
    @26
    cY
    cZ
    va
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    @36
    @59
    @123
    @60
    adantr
    #
    @36
    @61
    @123
    @62
    adantr
    #
    @36
    @63
    @123
    @64
    adantr
    #
    @36
    @66
    @123
    @67
    adantr
    #
    wph
    @33
    @34
    @123
    simplrl
    #
    wph
    @33
    @34
    @123
    simplrr
    #
    yoneda.m
    yonedalem3a
    simpld
    fveq1d
    @124
    @119
    @52
    wcel
    @125
    @127
    wceq
    @36
    @72
    @52
    @118
    @28
    @36
    vb
    vb
    @72
    @74
    @52
    @28
    cvv
    @77
    @73
    @28
    fvexd
    @110
    @78
    fmpt2d
    ffvelrnda
    va
    @119
    @56
    @127
    @52
    @57
    @54
    @119
    wceq
    @53
    @55
    @126
    @26
    @54
    @119
    fveq1
    fveq1d
    @57
    eqid
    #
    @53
    @126
    fvex
    fvmpt
    syl
    @124
    @127
    @118
    @53
    @26
    @26
    @85
    co
    #
    cfv
    #
    cfv
    @118
    cid
    @72
    cres
    #
    cfv
    #
    @118
    @124
    vx
    vy
    vu
    @118
    cB
    cC
    @26
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    vg
    cE
    @25
    @53
    cH
    cN
    cO
    cV
    cW
    @26
    cY
    cZ
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    @128
    @129
    @130
    @131
    @132
    @133
    yonedainv.n
    @36
    @123
    simpr
    @133
    @124
    cB
    cC
    c.1
    @81
    @26
    yoneda.b
    @81
    eqid
    #
    yoneda.1
    @128
    @133
    catidcl
    yonedalem4b
    @124
    @118
    @136
    @137
    @124
    @26
    cO
    ccid
    cfv
    #
    cfv
    #
    @135
    cfv
    @72
    cS
    ccid
    cfv
    #
    cfv
    @136
    @137
    @124
    cB
    cO
    @140
    cS
    @71
    @85
    @142
    @26
    @9
    @140
    eqid
    @142
    eqid
    #
    @124
    @0
    wrel
    #
    @33
    @71
    @85
    @0
    wbr
    #
    cO
    cS
    relfunc
    #
    @132
    @25
    @0
    1st2ndbr
    #
    sylancr
    #
    @133
    funcid
    @124
    @141
    @53
    @135
    @124
    @26
    @140
    c.1
    @124
    @59
    @140
    c.1
    wceq
    @128
    c.1
    cC
    cO
    yoneda.o
    yoneda.1
    oppcid
    syl
    fveq1d
    fveq2d
    @124
    cS
    cU
    @142
    cvv
    @72
    yoneda.s
    @143
    wph
    @113
    @35
    @123
    @114
    ad2antrr
    #
    @124
    cB
    cU
    @26
    @71
    @124
    cB
    cU
    @71
    wf
    #
    cB
    cS
    cbs
    cfv
    #
    @71
    wf
    #
    @124
    cB
    @151
    cO
    cS
    @71
    @85
    @9
    @151
    eqid
    #
    @148
    funcf1
    @124
    cU
    @151
    @71
    cB
    @124
    cS
    cU
    cvv
    yoneda.s
    @149
    setcbas
    feq3d
    mpbird
    @133
    ffvelrnd
    setcid
    3eqtr3d
    fveq1d
    @123
    @138
    @118
    wceq
    @36
    @72
    @118
    fvresi
    adantl
    3eqtrd
    3eqtrd
    syldan
    mpteq2dva
    vk
    @30
    mptresid
    syl6eq
    eqtrd
    @36
    @47
    vb
    @29
    @73
    @27
    cfv
    #
    @28
    cfv
    #
    cmpt
    #
    @48
    @36
    @44
    @43
    @47
    @156
    wceq
    @117
    @70
    vb
    @28
    @27
    @29
    @30
    @29
    fcompt
    syl2anc
    @36
    @156
    vb
    @29
    @73
    cmpt
    @48
    @36
    vb
    @29
    @155
    @73
    @36
    @73
    @29
    wcel
    #
    wa
    #
    vz
    cB
    @155
    @73
    @158
    @155
    cB
    cO
    cS
    @50
    c1st
    cfv
    #
    @50
    c2nd
    cfv
    #
    @71
    @85
    @51
    @51
    eqid
    #
    @158
    @155
    cO
    cS
    @50
    @25
    @51
    @161
    @158
    vx
    vy
    vu
    @154
    cB
    cC
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    vg
    cE
    @25
    cH
    cN
    cO
    cV
    cW
    @26
    cY
    cZ
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    @36
    @59
    @157
    @60
    adantr
    #
    @36
    @61
    @157
    @62
    adantr
    #
    @36
    @63
    @157
    @64
    adantr
    #
    @36
    @66
    @157
    @67
    adantr
    #
    wph
    @33
    @34
    @157
    simplrl
    #
    wph
    @33
    @34
    @157
    simplrr
    #
    yonedainv.n
    @36
    @29
    @72
    @73
    @27
    @36
    @43
    @29
    @72
    @27
    wf
    @70
    @36
    @30
    @72
    @27
    @29
    @115
    feq3d
    mpbid
    ffvelrnda
    #
    yonedalem4c
    nat1st2nd
    #
    @9
    natfn
    @158
    @73
    cB
    cO
    cS
    @159
    @160
    @71
    @85
    @51
    @161
    @158
    @73
    cO
    cS
    @50
    @25
    @51
    @161
    @36
    @157
    @73
    @52
    wcel
    #
    @36
    @29
    @52
    @73
    @116
    eleq2d
    biimpa
    #
    nat1st2nd
    #
    @9
    natfn
    @158
    @2
    cB
    wcel
    #
    wa
    #
    vk
    @2
    @159
    cfv
    #
    @118
    @2
    @155
    cfv
    #
    cfv
    #
    cmpt
    vk
    @175
    @118
    @2
    @73
    cfv
    #
    cfv
    #
    cmpt
    @176
    @178
    @174
    vk
    @175
    @177
    @179
    @174
    @118
    @175
    wcel
    #
    @118
    @2
    @26
    @81
    co
    #
    wcel
    #
    @177
    @179
    wceq
    @174
    @180
    @182
    @174
    @175
    @181
    @118
    @174
    cB
    cC
    @81
    @26
    cY
    @2
    yoneda.y
    yoneda.b
    @158
    @59
    @173
    @162
    adantr
    #
    @158
    @34
    @173
    @167
    adantr
    #
    @139
    @158
    @173
    simpr
    #
    yon11
    eleq2d
    biimpa
    @174
    @182
    wa
    #
    @177
    @154
    @118
    @26
    @2
    @85
    co
    #
    cfv
    #
    cfv
    @53
    @26
    @73
    cfv
    #
    cfv
    #
    @188
    cfv
    #
    @179
    @186
    vx
    vy
    vu
    @154
    cB
    cC
    @2
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    vg
    cE
    @25
    @118
    cH
    cN
    cO
    cV
    cW
    @26
    cY
    cZ
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    @174
    @59
    @182
    @183
    adantr
    #
    @158
    @61
    @173
    @182
    @163
    ad2antrr
    #
    @158
    @63
    @173
    @182
    @164
    ad2antrr
    #
    @158
    @66
    @173
    @182
    @165
    ad2antrr
    #
    @158
    @33
    @173
    @182
    @166
    ad2antrr
    #
    @174
    @34
    @182
    @184
    adantr
    #
    yonedainv.n
    @158
    @154
    @72
    wcel
    @173
    @182
    @168
    ad2antrr
    @158
    @173
    @182
    simplr
    #
    @174
    @182
    simpr
    #
    yonedalem4b
    @186
    @154
    @190
    @188
    @186
    @154
    @73
    @57
    cfv
    #
    @190
    @186
    @73
    @27
    @57
    @186
    @58
    @43
    @186
    vx
    cB
    cC
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    cE
    @25
    cH
    cM
    cO
    cV
    cW
    @26
    cY
    cZ
    va
    yoneda.y
    yoneda.b
    yoneda.1
    yoneda.o
    yoneda.s
    yoneda.t
    yoneda.q
    yoneda.h
    yoneda.r
    yoneda.e
    yoneda.z
    @192
    @193
    @194
    @195
    @196
    @197
    yoneda.m
    yonedalem3a
    simpld
    fveq1d
    @186
    @170
    @200
    @190
    wceq
    @158
    @170
    @173
    @182
    @171
    ad2antrr
    va
    @73
    @56
    @190
    @52
    @57
    va
    vb
    weq
    @53
    @55
    @189
    @26
    @54
    @73
    fveq1
    fveq1d
    @134
    @53
    @189
    fvex
    fvmpt
    syl
    eqtrd
    fveq2d
    @186
    @53
    @118
    @26
    @2
    @160
    co
    #
    cfv
    #
    cfv
    #
    @178
    cfv
    #
    @191
    @179
    @186
    @53
    @178
    @202
    ccom
    #
    cfv
    #
    @53
    @188
    @189
    ccom
    #
    cfv
    #
    @204
    @191
    @186
    @53
    @205
    @207
    @186
    @178
    @202
    @26
    @159
    cfv
    #
    @175
    cop
    @2
    @71
    cfv
    #
    cS
    cco
    cfv
    #
    co
    co
    @188
    @189
    @209
    @72
    cop
    @210
    @211
    co
    co
    @205
    @207
    @186
    @73
    cB
    cO
    cS
    @118
    @211
    @159
    @160
    cO
    chom
    cfv
    #
    @71
    @85
    @51
    @26
    @2
    @161
    @158
    @73
    @159
    @160
    cop
    @71
    @85
    cop
    @51
    co
    #
    wcel
    #
    @173
    @182
    @172
    ad2antrr
    @9
    @212
    eqid
    #
    @211
    eqid
    #
    @197
    @198
    @186
    @118
    @181
    @26
    @2
    @212
    co
    #
    @199
    cC
    @81
    cO
    @26
    @2
    @139
    yoneda.o
    oppchom
    syl6eleqr
    #
    nati
    @186
    cS
    @211
    cU
    @202
    @178
    cvv
    @209
    @175
    @210
    yoneda.s
    @174
    @113
    @182
    @158
    @113
    @173
    wph
    @113
    @35
    @157
    @114
    ad2antrr
    #
    adantr
    #
    adantr
    #
    @216
    @158
    @209
    cU
    wcel
    @173
    @182
    @158
    cB
    cU
    @26
    @159
    @158
    cB
    cU
    @159
    wf
    cB
    @151
    @159
    wf
    @158
    cB
    @151
    cO
    cS
    @159
    @160
    @9
    @153
    @158
    @144
    @50
    @0
    wcel
    @159
    @160
    @0
    wbr
    #
    @146
    @158
    cB
    @0
    @26
    @49
    wph
    cB
    @0
    @49
    wf
    @35
    @157
    wph
    cB
    @0
    cC
    cQ
    @49
    cY
    c2nd
    cfv
    #
    yoneda.b
    @8
    wph
    cC
    cQ
    cfunc
    co
    #
    wrel
    cY
    @224
    wcel
    @49
    @223
    @224
    wbr
    cC
    cQ
    relfunc
    wph
    cC
    cQ
    cS
    cU
    cO
    cvv
    cY
    yoneda.y
    yoneda.c
    yoneda.o
    yoneda.s
    yoneda.q
    @114
    yoneda.u
    yoncl
    cY
    @224
    1st2ndbr
    sylancr
    funcf1
    ad2antrr
    @167
    ffvelrnd
    @50
    @0
    1st2ndbr
    sylancr
    #
    funcf1
    @158
    cU
    @151
    @159
    cB
    @158
    cS
    cU
    cvv
    yoneda.s
    @219
    setcbas
    #
    feq3d
    mpbird
    #
    @167
    ffvelrnd
    #
    ad2antrr
    #
    @174
    @175
    cU
    wcel
    @182
    @158
    cB
    cU
    @2
    @159
    @227
    ffvelrnda
    #
    adantr
    #
    @174
    @210
    cU
    wcel
    @182
    @158
    cB
    cU
    @2
    @71
    @158
    @150
    @152
    @158
    cB
    @151
    cO
    cS
    @71
    @85
    @9
    @153
    @158
    @144
    @33
    @145
    @146
    @166
    @147
    sylancr
    funcf1
    @158
    cU
    @151
    @71
    cB
    @226
    feq3d
    mpbird
    #
    ffvelrnda
    #
    adantr
    #
    @186
    @202
    @209
    @175
    cS
    chom
    cfv
    #
    co
    #
    wcel
    @209
    @175
    @202
    wf
    #
    @186
    @217
    @236
    @118
    @201
    @186
    cB
    cO
    cS
    @159
    @160
    @212
    @235
    @26
    @2
    @9
    @215
    @235
    eqid
    #
    @158
    @222
    @173
    @182
    @225
    ad2antrr
    @197
    @198
    funcf2
    @218
    ffvelrnd
    @186
    cS
    cU
    @202
    @235
    cvv
    @209
    @175
    yoneda.s
    @221
    @238
    @229
    @231
    elsetchom
    mpbid
    #
    @174
    @175
    @210
    @178
    wf
    #
    @182
    @174
    @178
    @175
    @210
    @235
    co
    #
    wcel
    @240
    @174
    @73
    cB
    cO
    cS
    @159
    @160
    @235
    @71
    @85
    @51
    @2
    @161
    @158
    @214
    @173
    @172
    adantr
    @9
    @238
    @185
    natcl
    @174
    cS
    cU
    @178
    @235
    cvv
    @175
    @210
    yoneda.s
    @220
    @238
    @230
    @233
    elsetchom
    mpbid
    #
    adantr
    setcco
    @186
    cS
    @211
    cU
    @189
    @188
    cvv
    @209
    @72
    @210
    yoneda.s
    @221
    @216
    @229
    @158
    @72
    cU
    wcel
    @173
    @182
    @158
    cB
    cU
    @26
    @71
    @232
    @167
    ffvelrnd
    #
    ad2antrr
    #
    @234
    @158
    @209
    @72
    @189
    wf
    #
    @173
    @182
    @158
    @189
    @209
    @72
    @235
    co
    wcel
    @245
    @158
    @73
    cB
    cO
    cS
    @159
    @160
    @235
    @71
    @85
    @51
    @26
    @161
    @172
    @9
    @238
    @167
    natcl
    @158
    cS
    cU
    @189
    @235
    cvv
    @209
    @72
    yoneda.s
    @219
    @238
    @228
    @243
    elsetchom
    mpbid
    #
    ad2antrr
    @186
    @188
    @72
    @210
    @235
    co
    #
    wcel
    @72
    @210
    @188
    wf
    @186
    @217
    @247
    @118
    @187
    @186
    cB
    cO
    cS
    @71
    @85
    @212
    @235
    @26
    @2
    @9
    @215
    @238
    @186
    @144
    @33
    @145
    @146
    @196
    @147
    sylancr
    @197
    @198
    funcf2
    @218
    ffvelrnd
    @186
    cS
    cU
    @188
    @235
    cvv
    @72
    @210
    yoneda.s
    @221
    @238
    @244
    @234
    elsetchom
    mpbid
    setcco
    3eqtr3d
    fveq1d
    @186
    @237
    @53
    @209
    wcel
    #
    @206
    @204
    wceq
    @239
    @158
    @248
    @173
    @182
    @158
    @53
    @26
    @26
    @81
    co
    #
    @209
    @158
    cB
    cC
    c.1
    @81
    @26
    yoneda.b
    @139
    yoneda.1
    @162
    @167
    catidcl
    #
    @158
    cB
    cC
    @81
    @26
    cY
    @26
    yoneda.y
    yoneda.b
    @162
    @167
    @139
    @167
    yon11
    eleqtrrd
    #
    ad2antrr
    @209
    @175
    @53
    @178
    @202
    fvco3
    syl2anc
    @158
    @208
    @191
    wceq
    #
    @173
    @182
    @158
    @245
    @248
    @252
    @246
    @251
    @209
    @72
    @53
    @188
    @189
    fvco3
    syl2anc
    ad2antrr
    3eqtr3d
    @186
    @203
    @118
    @178
    @186
    @203
    @53
    @118
    @2
    @26
    cop
    @26
    cC
    cco
    cfv
    #
    co
    co
    @118
    @186
    cB
    cC
    @253
    @118
    @53
    @81
    @2
    @26
    cY
    @26
    yoneda.y
    yoneda.b
    @192
    @197
    @139
    @197
    @253
    eqid
    #
    @198
    @199
    @158
    @53
    @249
    wcel
    @173
    @182
    @250
    ad2antrr
    yon12
    @186
    cB
    cC
    @253
    c.1
    @118
    @81
    @2
    @26
    yoneda.b
    @139
    yoneda.1
    @192
    @198
    @254
    @197
    @199
    catlid
    eqtrd
    fveq2d
    eqtr3d
    3eqtrd
    syldan
    mpteq2dva
    @174
    vk
    @175
    @210
    @176
    @174
    @176
    @241
    wcel
    @175
    @210
    @176
    wf
    @174
    @155
    cB
    cO
    cS
    @159
    @160
    @235
    @71
    @85
    @51
    @2
    @161
    @158
    @155
    @213
    wcel
    @173
    @169
    adantr
    @9
    @238
    @185
    natcl
    @174
    cS
    cU
    @176
    @235
    cvv
    @175
    @210
    yoneda.s
    @220
    @238
    @230
    @233
    elsetchom
    mpbid
    feqmptd
    @174
    vk
    @175
    @210
    @178
    @242
    feqmptd
    3eqtr4d
    eqfnfvd
    mpteq2dva
    vb
    @29
    mptresid
    syl6eq
    eqtrd
    @29
    @30
    @27
    @28
    fcof1o
    syl22anc
    @41
    @39
    @37
    @38
    @28
    eqcom
    anbi2i
    sylib
    @36
    cT
    cV
    @27
    @28
    @6
    cW
    @29
    @30
    yoneda.t
    @62
    wph
    @25
    @26
    cV
    @0
    cB
    @19
    wph
    @1
    cV
    @19
    wf
    @1
    cT
    cbs
    cfv
    #
    @19
    wf
    wph
    @1
    @255
    @5
    cT
    @19
    cZ
    c2nd
    cfv
    #
    @10
    @255
    eqid
    #
    wph
    @11
    wrel
    #
    @12
    @19
    @256
    @11
    wbr
    @5
    cT
    relfunc
    #
    @15
    cZ
    @11
    1st2ndbr
    sylancr
    funcf1
    wph
    cV
    @255
    @19
    @1
    wph
    cT
    cV
    cW
    yoneda.t
    yoneda.w
    setcbas
    #
    feq3d
    mpbird
    fovrnda
    wph
    @25
    @26
    cV
    @0
    cB
    @21
    wph
    @1
    cV
    @21
    wf
    @1
    @255
    @21
    wf
    wph
    @1
    @255
    @5
    cT
    @21
    cE
    c2nd
    cfv
    #
    @10
    @257
    wph
    @258
    @13
    @21
    @261
    @11
    wbr
    @259
    @16
    cE
    @11
    1st2ndbr
    sylancr
    funcf1
    wph
    cV
    @255
    @21
    @1
    @260
    feq3d
    mpbird
    fovrnda
    @17
    setcinv
    mpbird
    ralrimivva
    @24
    @32
    vz
    vh
    vw
    @0
    cB
    @2
    @25
    @26
    cop
    #
    wceq
    #
    @18
    @27
    @3
    @28
    @23
    @31
    @263
    @18
    @262
    cM
    cfv
    @27
    @2
    @262
    cM
    fveq2
    @25
    @26
    cM
    df-ov
    syl6eqr
    @263
    @20
    @29
    @22
    @30
    @6
    @263
    @20
    @262
    @19
    cfv
    @29
    @2
    @262
    @19
    fveq2
    @25
    @26
    @19
    df-ov
    syl6eqr
    @263
    @22
    @262
    @21
    cfv
    @30
    @2
    @262
    @21
    fveq2
    @25
    @26
    @21
    df-ov
    syl6eqr
    oveq12d
    @263
    @3
    @262
    cN
    cfv
    @28
    @2
    @262
    cN
    fveq2
    @25
    @26
    cN
    df-ov
    syl6eqr
    breq123d
    ralxp
    sylibr
    r19.21bi
    invfuc
    cN
    @1
    wfn
    cN
    @4
    wceq
    vf
    vx
    @0
    cB
    @103
    cN
    yonedainv.n
    vu
    @95
    @102
    @92
    @94
    fvex
    mptex
    fnmpt2i
    vz
    @1
    cN
    dffn5
    mpbi
    syl6breqr
end
