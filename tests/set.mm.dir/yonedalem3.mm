include "cxpc.mm"
include "co.mm"
include "cnat.mm"
include "wcel.mm"
include "cfunc.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "chom.mm"
include "cixp.mm"
include "c2nd.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "wral.mm"
include "wfn.mm"
include "cmpt.mm"
include "ovex.mm"
include "mptex.mm"
include "fnmpt2i.mm"
include "a1i.mm"
include "wa.mm"
include "wf.mm"
include "ccat.mm"
include "adantr.mm"
include "chomf.mm"
include "crn.mm"
include "wss.mm"
include "cun.mm"
include "simprl.mm"
include "simprr.mm"
include "yonedalem3a.mm"
include "simprd.mm"
include "eqid.mm"
include "cbs.mm"
include "fucbas.mm"
include "oppcbas.mm"
include "xpcbas.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "yonedalem1.mm"
include "simpld.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "fovrnda.mm"
include "setcbas.mm"
include "eleqtrrd.mm"
include "elsetchom.mm"
include "mpbird.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "cmpt2.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "elixp.mm"
include "sylanbrc.mm"
include "w3a.mm"
include "simpr1.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "simpr2.mm"
include "simpr3.mm"
include "fuchom.mm"
include "xpchom.mm"
include "oppchom.mm"
include "xpeq2i.mm"
include "syl6eq.mm"
include "eleqtrd.mm"
include "yonedalem3b.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "fveq12d.mm"
include "oveq123d.mm"
include "3eqtr4d.mm"
include "ralrimivvva.mm"
include "isnat2.mm"
include "mpbir2and.mm"

theorem yonedalem3
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.1: class .1.
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vy: setvar y
  let vh: setvar h
  let vk: setvar k
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vv: setvar v
  let cF: class F
  let cK: class K
  let cG: class G
  let cN: class N
  let cI: class I
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

  disjoint a f
  disjoint a x
  disjoint .1. a
  disjoint f x
  disjoint .1. f
  disjoint .1. x
  disjoint C a
  disjoint C f
  disjoint C x
  disjoint E a
  disjoint E f
  disjoint B a
  disjoint B f
  disjoint B x
  disjoint O a
  disjoint O f
  disjoint O x
  disjoint S a
  disjoint S f
  disjoint S x
  disjoint Q a
  disjoint Q f
  disjoint Q x
  disjoint T f
  disjoint a ph
  disjoint f ph
  disjoint ph x
  disjoint Y a
  disjoint Y f
  disjoint Y x
  disjoint Z a
  disjoint Z f
  disjoint Z x
  disjoint a b
  disjoint a g
  disjoint a y
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint .1. b
  disjoint f g
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint .1. g
  disjoint x y
  disjoint .1. y
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
  disjoint g u
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
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint f h
  disjoint f u
  disjoint f w
  disjoint f z
  disjoint C g
  disjoint h x
  disjoint C h
  disjoint u x
  disjoint C u
  disjoint w x
  disjoint C w
  disjoint x z
  disjoint C y
  disjoint C z
  disjoint a v
  disjoint b v
  disjoint E b
  disjoint f k
  disjoint f v
  disjoint g v
  disjoint E g
  disjoint h v
  disjoint E h
  disjoint k v
  disjoint E k
  disjoint u v
  disjoint E u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint E v
  disjoint E w
  disjoint E y
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
  disjoint B g
  disjoint B h
  disjoint B k
  disjoint B u
  disjoint v x
  disjoint B v
  disjoint B w
  disjoint B y
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
  disjoint O b
  disjoint O g
  disjoint O h
  disjoint O k
  disjoint O u
  disjoint O v
  disjoint O w
  disjoint O y
  disjoint O z
  disjoint S b
  disjoint S g
  disjoint S h
  disjoint S k
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint M b
  disjoint M g
  disjoint M h
  disjoint M k
  disjoint M u
  disjoint M w
  disjoint M y
  disjoint M z
  disjoint Q b
  disjoint Q g
  disjoint Q u
  disjoint Q v
  disjoint Q w
  disjoint Q z
  disjoint T g
  disjoint T h
  disjoint T u
  disjoint T v
  disjoint T w
  disjoint T y
  disjoint T z
  disjoint P a
  disjoint P b
  disjoint P f
  disjoint P g
  disjoint P x
  disjoint P y
  disjoint b ph
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint R u
  disjoint R v
  disjoint R z
  disjoint Y b
  disjoint Y g
  disjoint Y h
  disjoint Y k
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y y
  disjoint Y z
  disjoint Z b
  disjoint Z g
  disjoint Z h
  disjoint Z k
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z y
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
  assert |- ( ph -> M e. ( Z ( ( Q Xc. O ) Nat T ) E ) )

  proof
    wph
    cM
    cZ
    cE
    cQ
    cO
    cxpc
    co
    #
    cT
    cnat
    co
    #
    co
    wcel
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
    cZ
    c1st
    cfv
    #
    cfv
    #
    @4
    cE
    c1st
    cfv
    #
    cfv
    #
    cT
    chom
    cfv
    #
    co
    #
    cixp
    wcel
    #
    vw
    cv
    #
    cM
    cfv
    #
    vg
    cv
    #
    @4
    @12
    cZ
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @6
    @12
    @5
    cfv
    #
    cop
    #
    @12
    @7
    cfv
    #
    cT
    cco
    cfv
    #
    co
    #
    co
    #
    @14
    @4
    @12
    cE
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @4
    cM
    cfv
    #
    @6
    @8
    cop
    #
    @20
    @21
    co
    #
    co
    #
    wceq
    #
    vg
    @4
    @12
    @0
    chom
    cfv
    #
    co
    #
    wral
    vw
    @3
    wral
    vz
    @3
    wral
    wph
    cM
    @3
    wfn
    #
    @27
    @10
    wcel
    #
    vz
    @3
    wral
    #
    @11
    @34
    wph
    vf
    vx
    @2
    cB
    va
    vx
    cv
    #
    cY
    c1st
    cfv
    #
    cfv
    #
    vf
    cv
    #
    cO
    cS
    cnat
    co
    #
    co
    #
    @37
    c.1
    cfv
    @37
    va
    cv
    #
    cfv
    cfv
    #
    cmpt
    #
    cM
    yoneda.m
    va
    @42
    @44
    @39
    @40
    @41
    ovex
    mptex
    fnmpt2i
    a1i
    wph
    @14
    vy
    cv
    #
    cM
    co
    #
    @14
    @46
    @5
    co
    #
    @14
    @46
    @7
    co
    #
    @9
    co
    #
    wcel
    #
    vy
    cB
    wral
    vg
    @2
    wral
    @36
    wph
    @51
    vg
    vy
    @2
    cB
    wph
    @14
    @2
    wcel
    #
    @46
    cB
    wcel
    #
    wa
    #
    wa
    #
    @51
    @48
    @49
    @47
    wf
    #
    @55
    @47
    va
    @46
    @38
    cfv
    @14
    @41
    co
    @46
    c.1
    cfv
    @46
    @43
    cfv
    cfv
    cmpt
    wceq
    @56
    @55
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
    @14
    cH
    cM
    cO
    cV
    cW
    @46
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
    @54
    yoneda.c
    adantr
    wph
    cV
    cW
    wcel
    #
    @54
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
    @54
    yoneda.u
    adantr
    wph
    cQ
    chomf
    cfv
    crn
    cU
    cun
    cV
    wss
    #
    @54
    yoneda.v
    adantr
    wph
    @52
    @53
    simprl
    wph
    @52
    @53
    simprr
    yoneda.m
    yonedalem3a
    simprd
    @55
    cT
    cV
    @47
    @9
    cW
    @48
    @49
    yoneda.t
    @59
    @9
    eqid
    #
    @55
    @48
    cT
    cbs
    cfv
    #
    cV
    wph
    @14
    @46
    @63
    @2
    cB
    @5
    wph
    @3
    @63
    @0
    cT
    @5
    @15
    cQ
    cO
    @0
    @2
    cB
    @0
    eqid
    #
    cO
    cS
    cQ
    yoneda.q
    fucbas
    cB
    cC
    cO
    yoneda.o
    yoneda.b
    oppcbas
    xpcbas
    #
    @63
    eqid
    #
    wph
    @0
    cT
    cfunc
    co
    #
    wrel
    #
    cZ
    @67
    wcel
    #
    @5
    @15
    @67
    wbr
    @0
    cT
    relfunc
    #
    wph
    @69
    cE
    @67
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
    cZ
    @67
    1st2ndbr
    sylancr
    funcf1
    fovrnda
    @55
    cT
    cV
    cW
    yoneda.t
    @59
    setcbas
    #
    eleqtrrd
    @55
    @49
    @63
    cV
    wph
    @14
    @46
    @63
    @2
    cB
    @7
    wph
    @3
    @63
    @0
    cT
    @7
    @24
    @65
    @66
    wph
    @68
    @71
    @7
    @24
    @67
    wbr
    @70
    wph
    @69
    @71
    @72
    simprd
    #
    cE
    @67
    1st2ndbr
    sylancr
    funcf1
    fovrnda
    @74
    eleqtrrd
    elsetchom
    mpbird
    ralrimivva
    @35
    @51
    vz
    vg
    vy
    @2
    cB
    @4
    @14
    @46
    cop
    #
    wceq
    #
    @27
    @47
    @10
    @50
    @77
    @27
    @76
    cM
    cfv
    @47
    @4
    @76
    cM
    fveq2
    @14
    @46
    cM
    df-ov
    syl6eqr
    @77
    @6
    @48
    @8
    @49
    @9
    @77
    @6
    @76
    @5
    cfv
    @48
    @4
    @76
    @5
    fveq2
    @14
    @46
    @5
    df-ov
    syl6eqr
    @77
    @8
    @76
    @7
    cfv
    @49
    @4
    @76
    @7
    fveq2
    @14
    @46
    @7
    df-ov
    syl6eqr
    oveq12d
    eleq12d
    ralxp
    sylibr
    vz
    @3
    @10
    cM
    cM
    vf
    vx
    @2
    cB
    @45
    cmpt2
    cvv
    yoneda.m
    vf
    vx
    @2
    cB
    @45
    cO
    cS
    cfunc
    ovex
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
    mpt2ex
    eqeltri
    elixp
    sylanbrc
    wph
    @31
    vz
    vw
    vg
    @3
    @3
    @33
    wph
    @4
    @3
    wcel
    #
    @12
    @3
    wcel
    #
    @14
    @33
    wcel
    #
    w3a
    #
    wa
    #
    @12
    c1st
    cfv
    #
    @12
    c2nd
    cfv
    #
    cM
    co
    #
    @14
    c1st
    cfv
    #
    @14
    c2nd
    cfv
    #
    @4
    c1st
    cfv
    #
    @4
    c2nd
    cfv
    #
    cop
    #
    @83
    @84
    cop
    #
    @15
    co
    #
    co
    #
    @88
    @89
    @5
    co
    #
    @83
    @84
    @5
    co
    #
    cop
    #
    @83
    @84
    @7
    co
    #
    @21
    co
    #
    co
    @86
    @87
    @90
    @91
    @24
    co
    #
    co
    #
    @88
    @89
    cM
    co
    #
    @94
    @88
    @89
    @7
    co
    #
    cop
    #
    @97
    @21
    co
    #
    co
    @23
    @30
    @82
    vx
    @86
    cB
    cC
    @84
    cQ
    cR
    cS
    cT
    cU
    c.1
    vf
    cE
    @88
    @83
    cH
    @87
    cM
    cO
    cV
    cW
    @89
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
    @57
    @81
    yoneda.c
    adantr
    wph
    @58
    @81
    yoneda.w
    adantr
    wph
    @60
    @81
    yoneda.u
    adantr
    wph
    @61
    @81
    yoneda.v
    adantr
    @82
    @78
    @88
    @2
    wcel
    wph
    @78
    @79
    @80
    simpr1
    #
    @4
    @2
    cB
    xp1st
    syl
    @82
    @78
    @89
    cB
    wcel
    @105
    @4
    @2
    cB
    xp2nd
    syl
    @82
    @79
    @83
    @2
    wcel
    wph
    @78
    @79
    @80
    simpr2
    #
    @12
    @2
    cB
    xp1st
    syl
    @82
    @79
    @84
    cB
    wcel
    @106
    @12
    @2
    cB
    xp2nd
    syl
    @82
    @14
    @88
    @83
    @41
    co
    #
    @84
    @89
    cC
    chom
    cfv
    #
    co
    #
    cxp
    #
    wcel
    #
    @86
    @107
    wcel
    @82
    @14
    @33
    @110
    wph
    @78
    @79
    @80
    simpr3
    @82
    @33
    @107
    @89
    @84
    cO
    chom
    cfv
    #
    co
    #
    cxp
    @110
    @82
    @3
    cQ
    cO
    @0
    @41
    @112
    @32
    @4
    @12
    @64
    @65
    cO
    cS
    cQ
    @41
    yoneda.q
    @41
    eqid
    fuchom
    @112
    eqid
    @32
    eqid
    #
    @105
    @106
    xpchom
    @113
    @109
    @107
    cC
    @108
    cO
    @89
    @84
    @108
    eqid
    yoneda.o
    oppchom
    xpeq2i
    syl6eq
    eleqtrd
    #
    @14
    @107
    @109
    xp1st
    syl
    @82
    @111
    @87
    @109
    wcel
    @115
    @14
    @107
    @109
    xp2nd
    syl
    yoneda.m
    yonedalem3b
    @82
    @13
    @85
    @17
    @93
    @22
    @98
    @82
    @19
    @96
    @20
    @97
    @21
    @82
    @6
    @94
    @18
    @95
    @82
    @6
    @90
    @5
    cfv
    @94
    @82
    @4
    @90
    @5
    @82
    @78
    @4
    @90
    wceq
    @105
    @4
    @2
    cB
    1st2nd2
    syl
    #
    fveq2d
    @88
    @89
    @5
    df-ov
    syl6eqr
    #
    @82
    @18
    @91
    @5
    cfv
    @95
    @82
    @12
    @91
    @5
    @82
    @79
    @12
    @91
    wceq
    @106
    @12
    @2
    cB
    1st2nd2
    syl
    #
    fveq2d
    @83
    @84
    @5
    df-ov
    syl6eqr
    opeq12d
    @82
    @20
    @91
    @7
    cfv
    @97
    @82
    @12
    @91
    @7
    @118
    fveq2d
    @83
    @84
    @7
    df-ov
    syl6eqr
    #
    oveq12d
    @82
    @13
    @91
    cM
    cfv
    @85
    @82
    @12
    @91
    cM
    @118
    fveq2d
    @83
    @84
    cM
    df-ov
    syl6eqr
    @82
    @17
    @86
    @87
    cop
    #
    @92
    cfv
    @93
    @82
    @14
    @120
    @16
    @92
    @82
    @4
    @90
    @12
    @91
    @15
    @116
    @118
    oveq12d
    @82
    @111
    @14
    @120
    wceq
    @115
    @14
    @107
    @109
    1st2nd2
    syl
    #
    fveq12d
    @86
    @87
    @92
    df-ov
    syl6eqr
    oveq123d
    @82
    @26
    @100
    @27
    @101
    @29
    @104
    @82
    @28
    @103
    @20
    @97
    @21
    @82
    @6
    @94
    @8
    @102
    @117
    @82
    @8
    @90
    @7
    cfv
    @102
    @82
    @4
    @90
    @7
    @116
    fveq2d
    @88
    @89
    @7
    df-ov
    syl6eqr
    opeq12d
    @119
    oveq12d
    @82
    @26
    @120
    @99
    cfv
    @100
    @82
    @14
    @120
    @25
    @99
    @82
    @4
    @90
    @12
    @91
    @24
    @116
    @118
    oveq12d
    @121
    fveq12d
    @86
    @87
    @99
    df-ov
    syl6eqr
    @82
    @27
    @90
    cM
    cfv
    @101
    @82
    @4
    @90
    cM
    @116
    fveq2d
    @88
    @89
    cM
    df-ov
    syl6eqr
    oveq123d
    3eqtr4d
    ralrimivvva
    wph
    vz
    vw
    cM
    @3
    @0
    cT
    @21
    vg
    cZ
    cE
    @32
    @9
    @1
    @1
    eqid
    @65
    @114
    @62
    @21
    eqid
    @73
    @75
    isnat2
    mpbir2and
end
