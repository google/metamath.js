include "co.mm"
include "cfv.mm"
include "c1st.mm"
include "cnat.mm"
include "wcel.mm"
include "cv.mm"
include "chom.mm"
include "cixp.mm"
include "c2nd.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "wral.mm"
include "cmpt.mm"
include "yonedalem4a.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "fveq1d.mm"
include "mpteq12dv.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "wa.mm"
include "wf.mm"
include "oppcbas.mm"
include "eqid.mm"
include "cfunc.mm"
include "wbr.mm"
include "wrel.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "adantr.mm"
include "simpr.mm"
include "funcf2.mm"
include "oppchom.mm"
include "syl6eleqr.mm"
include "ffvelrnd.mm"
include "cvv.mm"
include "chomf.mm"
include "crn.mm"
include "unssbd.mm"
include "ssexd.mm"
include "cbs.mm"
include "funcf1.mm"
include "setcbas.mm"
include "feq3d.mm"
include "mpbird.mm"
include "ad2antrr.mm"
include "ffvelrnda.mm"
include "elsetchom.mm"
include "mpbid.mm"
include "fmptd.mm"
include "ccat.mm"
include "yon11.mm"
include "feq2d.mm"
include "yon1cl.mm"
include "ralrimiva.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptelixpg.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "ccom.mm"
include "simpr1.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "simpr2.mm"
include "simplr3.mm"
include "funcco.mm"
include "oppcco.mm"
include "fveq2d.mm"
include "3ad2antr1.mm"
include "simpr3.mm"
include "setcco.mm"
include "3eqtr3d.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "syl6eleq.mm"
include "yon12.mm"
include "wss.mm"
include "cun.mm"
include "catcocl.mm"
include "yonedalem4b.mm"
include "3eqtr4d.mm"
include "syldan.mm"
include "mpteq2dva.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "feq1d.mm"
include "fveq2.mm"
include "feq123d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fcompt.mm"
include "ralrimivvva.mm"
include "isnat2.mm"
include "mpbir2and.mm"

theorem yonedalem4c
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
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
  let cF: class F
  let cH: class H
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vh: setvar h
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  let cK: class K
  let cG: class G
  let cI: class I
  let cM: class M
  let cP: class P
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
  assume yonedalem21.f: |- ( ph -> F e. ( O Func S ) )
  assume yonedalem21.x: |- ( ph -> X e. B )
  assume yonedalem4.n: |- N = ( f e. ( O Func S ) , x e. B |-> ( u e. ( ( 1st ` f ) ` x ) |-> ( y e. B |-> ( g e. ( y ( Hom ` C ) x ) |-> ( ( ( x ( 2nd ` f ) y ) ` g ) ` u ) ) ) ) )
  assume yonedalem4.p: |- ( ph -> A e. ( ( 1st ` F ) ` X ) )

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
  disjoint g u
  disjoint A g
  disjoint u y
  disjoint A u
  disjoint A y
  disjoint f u
  disjoint C f
  disjoint C g
  disjoint u x
  disjoint C u
  disjoint C x
  disjoint C y
  disjoint E f
  disjoint E g
  disjoint E u
  disjoint E y
  disjoint F f
  disjoint F g
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint B f
  disjoint B g
  disjoint B u
  disjoint B x
  disjoint B y
  disjoint O f
  disjoint O g
  disjoint O u
  disjoint O x
  disjoint O y
  disjoint S f
  disjoint S g
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint Q f
  disjoint Q g
  disjoint Q u
  disjoint Q x
  disjoint T f
  disjoint T g
  disjoint T u
  disjoint T y
  disjoint f ph
  disjoint g ph
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint R u
  disjoint Y f
  disjoint Y g
  disjoint Y u
  disjoint Y x
  disjoint Y y
  disjoint Z f
  disjoint Z g
  disjoint Z u
  disjoint Z x
  disjoint Z y
  disjoint X f
  disjoint X g
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint .1. a
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint .1. b
  disjoint a h
  disjoint a k
  disjoint a u
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
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A z
  disjoint C a
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
  disjoint E a
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
  disjoint F h
  disjoint k x
  disjoint F k
  disjoint F w
  disjoint F z
  disjoint K a
  disjoint K b
  disjoint K y
  disjoint B a
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
  disjoint N a
  disjoint N b
  disjoint N h
  disjoint N k
  disjoint N v
  disjoint N w
  disjoint N z
  disjoint I z
  disjoint O a
  disjoint O b
  disjoint O h
  disjoint O k
  disjoint O v
  disjoint O w
  disjoint O z
  disjoint S a
  disjoint S b
  disjoint S h
  disjoint S k
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint M b
  disjoint M g
  disjoint M h
  disjoint M k
  disjoint M u
  disjoint M w
  disjoint M y
  disjoint M z
  disjoint Q a
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
  disjoint a ph
  disjoint b ph
  disjoint h ph
  disjoint k ph
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint R v
  disjoint R z
  disjoint Y a
  disjoint Y b
  disjoint Y h
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint Z a
  disjoint Z b
  disjoint Z h
  disjoint Z k
  disjoint Z v
  disjoint Z w
  disjoint Z z
  disjoint X a
  disjoint X b
  disjoint X h
  disjoint X k
  disjoint X w
  disjoint X z
  assert |- ( ph -> ( ( F N X ) ` A ) e. ( ( ( 1st ` Y ) ` X ) ( O Nat S ) F ) )

  proof
    wph
    cA
    cF
    cX
    cN
    co
    cfv
    #
    cX
    cY
    c1st
    cfv
    cfv
    #
    cF
    cO
    cS
    cnat
    co
    #
    co
    wcel
    @0
    vz
    cB
    vz
    cv
    #
    @1
    c1st
    cfv
    #
    cfv
    #
    @3
    cF
    c1st
    cfv
    #
    cfv
    #
    cS
    chom
    cfv
    #
    co
    #
    cixp
    #
    wcel
    vw
    cv
    #
    @0
    cfv
    #
    vh
    cv
    #
    @3
    @11
    @1
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @5
    @11
    @4
    cfv
    #
    cop
    @11
    @6
    cfv
    #
    cS
    cco
    cfv
    #
    co
    co
    #
    @13
    @3
    @11
    cF
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @3
    @0
    cfv
    #
    @5
    @7
    cop
    @18
    @19
    co
    co
    #
    wceq
    #
    vh
    @3
    @11
    cO
    chom
    cfv
    #
    co
    #
    wral
    vw
    cB
    wral
    vz
    cB
    wral
    wph
    @0
    vz
    cB
    vg
    @3
    cX
    cC
    chom
    cfv
    #
    co
    #
    cA
    vg
    cv
    #
    cX
    @3
    @21
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
    @10
    wph
    @0
    vy
    cB
    vg
    vy
    cv
    #
    cX
    @29
    co
    #
    cA
    @31
    cX
    @37
    @21
    co
    #
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    @36
    wph
    vx
    vy
    vu
    cA
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
    cF
    cH
    cN
    cO
    cV
    cW
    cX
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
    yonedalem21.f
    yonedalem21.x
    yonedalem4.n
    yonedalem4.p
    yonedalem4a
    vy
    vz
    cB
    @42
    @35
    vy
    vz
    weq
    #
    vg
    @38
    @41
    @30
    @34
    @37
    @3
    cX
    @29
    oveq1
    @43
    cA
    @40
    @33
    @43
    @31
    @39
    @32
    @37
    @3
    cX
    @21
    oveq2
    fveq1d
    fveq1d
    mpteq12dv
    cbvmptv
    syl6eq
    #
    wph
    @35
    @9
    wcel
    #
    vz
    cB
    wral
    #
    @36
    @10
    wcel
    #
    wph
    @45
    vz
    cB
    wph
    @3
    cB
    wcel
    #
    wa
    #
    @45
    @5
    @7
    @35
    wf
    #
    @49
    @50
    @30
    @7
    @35
    wf
    @49
    vg
    @30
    @34
    @7
    @35
    @49
    @31
    @30
    wcel
    #
    wa
    #
    cX
    @6
    cfv
    #
    @7
    cA
    @33
    @52
    @33
    @53
    @7
    @8
    co
    #
    wcel
    @53
    @7
    @33
    wf
    @52
    cX
    @3
    @27
    co
    #
    @54
    @31
    @32
    @49
    @55
    @54
    @32
    wf
    #
    @51
    @49
    cB
    cO
    cS
    @6
    @21
    @27
    @8
    cX
    @3
    cB
    cC
    cO
    yoneda.o
    yoneda.b
    oppcbas
    #
    @27
    eqid
    #
    @8
    eqid
    #
    wph
    @6
    @21
    cO
    cS
    cfunc
    co
    #
    wbr
    #
    @48
    wph
    @60
    wrel
    #
    cF
    @60
    wcel
    #
    @61
    cO
    cS
    relfunc
    #
    yonedalem21.f
    cF
    @60
    1st2ndbr
    sylancr
    #
    adantr
    wph
    cX
    cB
    wcel
    #
    @48
    yonedalem21.x
    adantr
    #
    wph
    @48
    simpr
    #
    funcf2
    adantr
    @52
    @31
    @30
    @55
    @49
    @51
    simpr
    cC
    @29
    cO
    cX
    @3
    @29
    eqid
    #
    yoneda.o
    oppchom
    #
    syl6eleqr
    ffvelrnd
    @52
    cS
    cU
    @33
    @8
    cvv
    @53
    @7
    yoneda.s
    @49
    cU
    cvv
    wcel
    #
    @51
    wph
    @71
    @48
    wph
    cU
    cV
    cW
    yoneda.w
    wph
    cQ
    chomf
    cfv
    crn
    #
    cU
    cV
    yoneda.v
    unssbd
    ssexd
    #
    adantr
    #
    adantr
    @59
    wph
    @53
    cU
    wcel
    #
    @48
    @51
    wph
    cB
    cU
    cX
    @6
    wph
    cB
    cU
    @6
    wf
    #
    cB
    cS
    cbs
    cfv
    #
    @6
    wf
    wph
    cB
    @77
    cO
    cS
    @6
    @21
    @57
    @77
    eqid
    #
    @65
    funcf1
    wph
    cU
    @77
    @6
    cB
    wph
    cS
    cU
    cvv
    yoneda.s
    @73
    setcbas
    #
    feq3d
    mpbird
    #
    yonedalem21.x
    ffvelrnd
    #
    ad2antrr
    @49
    @7
    cU
    wcel
    #
    @51
    wph
    cB
    cU
    @3
    @6
    @80
    ffvelrnda
    #
    adantr
    elsetchom
    mpbid
    wph
    cA
    @53
    wcel
    #
    @48
    @51
    yonedalem4.p
    ad2antrr
    ffvelrnd
    @35
    eqid
    fmptd
    @49
    @5
    @30
    @7
    @35
    @49
    cB
    cC
    @29
    cX
    cY
    @3
    yoneda.y
    yoneda.b
    wph
    cC
    ccat
    wcel
    #
    @48
    yoneda.c
    adantr
    @67
    @69
    @68
    yon11
    feq2d
    mpbird
    #
    @49
    cS
    cU
    @35
    @8
    cvv
    @5
    @7
    yoneda.s
    @74
    @59
    wph
    cB
    cU
    @3
    @4
    wph
    cB
    cU
    @4
    wf
    #
    cB
    @77
    @4
    wf
    wph
    cB
    @77
    cO
    cS
    @4
    @14
    @57
    @78
    wph
    @62
    @1
    @60
    wcel
    @4
    @14
    @60
    wbr
    #
    @64
    wph
    cB
    cC
    cS
    cU
    cO
    cvv
    cX
    cY
    yoneda.y
    yoneda.b
    yoneda.c
    yonedalem21.x
    yoneda.o
    yoneda.s
    @73
    yoneda.u
    yon1cl
    #
    @1
    @60
    1st2ndbr
    sylancr
    #
    funcf1
    wph
    cU
    @77
    @4
    cB
    @79
    feq3d
    mpbird
    #
    ffvelrnda
    #
    @83
    elsetchom
    mpbird
    ralrimiva
    cB
    cvv
    wcel
    @47
    @46
    wb
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
    vz
    cB
    @35
    @9
    cvv
    mptelixpg
    ax-mp
    sylibr
    eqeltrd
    wph
    @26
    vz
    vw
    vh
    cB
    cB
    @28
    wph
    @48
    @11
    cB
    wcel
    #
    @13
    @28
    wcel
    #
    w3a
    #
    wa
    #
    @12
    @16
    ccom
    #
    @23
    @24
    ccom
    #
    @20
    @25
    @96
    vk
    @5
    vk
    cv
    #
    @16
    cfv
    #
    @12
    cfv
    #
    cmpt
    #
    vk
    @5
    @99
    @24
    cfv
    #
    @23
    cfv
    #
    cmpt
    #
    @97
    @98
    @96
    vk
    @5
    @101
    @104
    @96
    @99
    @5
    wcel
    #
    @99
    @30
    wcel
    #
    @101
    @104
    wceq
    @96
    @106
    @107
    @96
    @5
    @30
    @99
    @96
    cB
    cC
    @29
    cX
    cY
    @3
    yoneda.y
    yoneda.b
    wph
    @85
    @95
    yoneda.c
    adantr
    #
    wph
    @66
    @95
    yonedalem21.x
    adantr
    #
    @69
    wph
    @48
    @93
    @94
    simpr1
    #
    yon11
    eleq2d
    biimpa
    @96
    @107
    wa
    #
    cA
    @99
    @13
    @11
    @3
    cop
    cX
    cC
    cco
    cfv
    #
    co
    co
    #
    cX
    @11
    @21
    co
    #
    cfv
    #
    cfv
    #
    cA
    @99
    @32
    cfv
    #
    cfv
    #
    @23
    cfv
    #
    @101
    @104
    @111
    @116
    cA
    @23
    @117
    ccom
    #
    cfv
    #
    @119
    @111
    cA
    @115
    @120
    @111
    @13
    @99
    cX
    @3
    cop
    @11
    cO
    cco
    cfv
    #
    co
    co
    #
    @114
    cfv
    @23
    @117
    @53
    @7
    cop
    @18
    @19
    co
    co
    @115
    @120
    @111
    cB
    cO
    @122
    cS
    @6
    @21
    @27
    @99
    @13
    @19
    cX
    @3
    @11
    @57
    @58
    @122
    eqid
    @19
    eqid
    #
    @96
    @61
    @107
    wph
    @61
    @95
    @65
    adantr
    #
    adantr
    @96
    @66
    @107
    @109
    adantr
    #
    @96
    @48
    @107
    @110
    adantr
    #
    @96
    @93
    @107
    wph
    @48
    @93
    @94
    simpr2
    #
    adantr
    #
    @111
    @99
    @30
    @55
    @96
    @107
    simpr
    #
    @70
    syl6eleqr
    #
    @48
    @93
    @94
    wph
    @107
    simplr3
    #
    funcco
    @111
    @123
    @113
    @114
    @111
    cB
    cC
    @112
    @99
    @13
    cO
    cX
    @3
    @11
    yoneda.b
    @112
    eqid
    #
    yoneda.o
    @126
    @127
    @129
    oppcco
    fveq2d
    @111
    cS
    @19
    cU
    @117
    @23
    cvv
    @53
    @7
    @18
    yoneda.s
    @96
    @71
    @107
    wph
    @71
    @95
    @73
    adantr
    #
    adantr
    #
    @124
    wph
    @75
    @95
    @107
    @81
    ad2antrr
    #
    @96
    @82
    @107
    wph
    @93
    @48
    @82
    @94
    @83
    3ad2antr1
    #
    adantr
    #
    @96
    @18
    cU
    wcel
    @107
    @96
    cB
    cU
    @11
    @6
    wph
    @76
    @95
    @80
    adantr
    @128
    ffvelrnd
    #
    adantr
    @111
    @117
    @54
    wcel
    @53
    @7
    @117
    wf
    #
    @111
    @55
    @54
    @99
    @32
    @96
    @56
    @107
    @96
    cB
    cO
    cS
    @6
    @21
    @27
    @8
    cX
    @3
    @57
    @58
    @59
    @125
    @109
    @110
    funcf2
    adantr
    @131
    ffvelrnd
    @111
    cS
    cU
    @117
    @8
    cvv
    @53
    @7
    yoneda.s
    @135
    @59
    @136
    @138
    elsetchom
    mpbid
    #
    @96
    @7
    @18
    @23
    wf
    #
    @107
    @96
    @23
    @7
    @18
    @8
    co
    #
    wcel
    @142
    @96
    @28
    @143
    @13
    @22
    @96
    cB
    cO
    cS
    @6
    @21
    @27
    @8
    @3
    @11
    @57
    @58
    @59
    @125
    @110
    @128
    funcf2
    wph
    @48
    @93
    @94
    simpr3
    #
    ffvelrnd
    @96
    cS
    cU
    @23
    @8
    cvv
    @7
    @18
    yoneda.s
    @134
    @59
    @137
    @139
    elsetchom
    mpbid
    #
    adantr
    setcco
    3eqtr3d
    fveq1d
    @111
    @140
    @84
    @121
    @119
    wceq
    @141
    wph
    @84
    @95
    @107
    yonedalem4.p
    ad2antrr
    #
    @53
    @7
    cA
    @23
    @117
    fvco3
    syl2anc
    eqtrd
    @111
    @101
    @113
    @12
    cfv
    @116
    @111
    @100
    @113
    @12
    @111
    cB
    cC
    @112
    @13
    @99
    @29
    @11
    cX
    cY
    @3
    yoneda.y
    yoneda.b
    @96
    @85
    @107
    @108
    adantr
    #
    @126
    @69
    @127
    @133
    @129
    @111
    @13
    @28
    @11
    @3
    @29
    co
    @132
    cC
    @29
    cO
    @3
    @11
    @69
    yoneda.o
    oppchom
    syl6eleq
    #
    @130
    yon12
    fveq2d
    @111
    vx
    vy
    vu
    cA
    cB
    cC
    @11
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    vg
    cE
    cF
    @113
    cH
    cN
    cO
    cV
    cW
    cX
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
    @147
    wph
    cV
    cW
    wcel
    @95
    @107
    yoneda.w
    ad2antrr
    #
    wph
    cC
    chomf
    cfv
    crn
    cU
    wss
    @95
    @107
    yoneda.u
    ad2antrr
    #
    wph
    @72
    cU
    cun
    cV
    wss
    @95
    @107
    yoneda.v
    ad2antrr
    #
    wph
    @63
    @95
    @107
    yonedalem21.f
    ad2antrr
    #
    @126
    yonedalem4.n
    @146
    @129
    @111
    cB
    cC
    @112
    @13
    @99
    @29
    @11
    @3
    cX
    yoneda.b
    @69
    @133
    @147
    @129
    @127
    @126
    @148
    @130
    catcocl
    yonedalem4b
    eqtrd
    @111
    @103
    @118
    @23
    @111
    vx
    vy
    vu
    cA
    cB
    cC
    @3
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    vg
    cE
    cF
    @99
    cH
    cN
    cO
    cV
    cW
    cX
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
    @147
    @149
    @150
    @151
    @152
    @126
    yonedalem4.n
    @146
    @127
    @130
    yonedalem4b
    fveq2d
    3eqtr4d
    syldan
    mpteq2dva
    @96
    @17
    @18
    @12
    wf
    #
    @5
    @17
    @16
    wf
    #
    @97
    @102
    wceq
    @96
    @93
    @5
    @7
    @24
    wf
    #
    vz
    cB
    wral
    #
    @153
    @128
    wph
    @156
    @95
    wph
    @155
    vz
    cB
    @49
    @155
    @50
    @86
    @49
    @5
    @7
    @24
    @35
    wph
    @48
    @24
    @3
    @36
    cfv
    #
    @35
    wph
    @3
    @0
    @36
    @44
    fveq1d
    @48
    @35
    cvv
    wcel
    @157
    @35
    wceq
    vg
    @30
    @34
    @3
    cX
    @29
    ovex
    mptex
    vz
    cB
    @35
    cvv
    @36
    @36
    eqid
    fvmpt2
    mpan2
    sylan9eq
    feq1d
    mpbird
    #
    ralrimiva
    adantr
    @155
    @153
    vz
    @11
    cB
    vz
    vw
    weq
    @5
    @17
    @7
    @18
    @24
    @12
    @3
    @11
    @0
    fveq2
    @3
    @11
    @4
    fveq2
    @3
    @11
    @6
    fveq2
    feq123d
    rspcv
    sylc
    #
    @96
    @16
    @5
    @17
    @8
    co
    #
    wcel
    @154
    @96
    @28
    @160
    @13
    @15
    @96
    cB
    cO
    cS
    @4
    @14
    @27
    @8
    @3
    @11
    @57
    @58
    @59
    wph
    @88
    @95
    @90
    adantr
    @110
    @128
    funcf2
    @144
    ffvelrnd
    @96
    cS
    cU
    @16
    @8
    cvv
    @5
    @17
    yoneda.s
    @134
    @59
    wph
    @93
    @48
    @5
    cU
    wcel
    @94
    @92
    3ad2antr1
    #
    @96
    cB
    cU
    @11
    @4
    wph
    @87
    @95
    @91
    adantr
    @128
    ffvelrnd
    #
    elsetchom
    mpbid
    #
    vk
    @12
    @16
    @5
    @17
    @18
    fcompt
    syl2anc
    @96
    @142
    @155
    @98
    @105
    wceq
    @145
    wph
    @93
    @48
    @155
    @94
    @158
    3ad2antr1
    #
    vk
    @23
    @24
    @5
    @7
    @18
    fcompt
    syl2anc
    3eqtr4d
    @96
    cS
    @19
    cU
    @16
    @12
    cvv
    @5
    @17
    @18
    yoneda.s
    @134
    @124
    @161
    @162
    @139
    @163
    @159
    setcco
    @96
    cS
    @19
    cU
    @24
    @23
    cvv
    @5
    @7
    @18
    yoneda.s
    @134
    @124
    @161
    @137
    @139
    @164
    @145
    setcco
    3eqtr4d
    ralrimivvva
    wph
    vz
    vw
    @0
    cB
    cO
    cS
    @19
    vh
    @1
    cF
    @27
    @8
    @2
    @2
    eqid
    @57
    @58
    @59
    @124
    @89
    yonedalem21.f
    isnat2
    mpbir2and
end
