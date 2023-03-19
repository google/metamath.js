include "co.mm"
include "cop.mm"
include "c2nd.mm"
include "cfv.mm"
include "ccom.mm"
include "c1st.mm"
include "cco.mm"
include "cnat.mm"
include "cv.mm"
include "cmpt.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "oppcbas.mm"
include "chom.mm"
include "fuchom.mm"
include "cfunc.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "cvv.mm"
include "chomf.mm"
include "crn.mm"
include "unssbd.mm"
include "ssexd.mm"
include "yoncl.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf2.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "simpr.mm"
include "fuccocl.mm"
include "fuccoval.mm"
include "wf.mm"
include "cbs.mm"
include "fucbas.mm"
include "funcf1.mm"
include "setcbas.mm"
include "feq3d.mm"
include "mpbird.mm"
include "eleqtrrd.mm"
include "nat1st2nd.mm"
include "natcl.mm"
include "elsetchom.mm"
include "mpbid.mm"
include "setcco.mm"
include "eqtrd.mm"
include "fco.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "catidcl.mm"
include "yon11.mm"
include "fvco3.mm"
include "ccat.mm"
include "yon2.mm"
include "catrid.mm"
include "fveq2d.mm"
include "oppchom.mm"
include "syl6eleqr.mm"
include "nati.mm"
include "3eqtr3d.mm"
include "yon12.mm"
include "catlid.mm"
include "3eqtr2d.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "wral.mm"
include "cxpc.mm"
include "cxp.mm"
include "xpcbas.mm"
include "yonedalem1.mm"
include "simpld.mm"
include "opelxpi.mm"
include "xpchom2.mm"
include "xpeq2i.mm"
include "syl6eq.mm"
include "df-ov.mm"
include "oveq12i.mm"
include "eqcomi.mm"
include "a1i.mm"
include "feq23d.mm"
include "fovrnd.mm"
include "yonedalem22.mm"
include "oppccat.mm"
include "syl.mm"
include "setccat.mm"
include "fuccat.mm"
include "hof2val.mm"
include "yonedalem21.mm"
include "feq123d.mm"
include "fmpt.mm"
include "sylibr.mm"
include "yonedalem3a.mm"
include "fveq1.mm"
include "fmptcof.mm"
include "evlf2val.mm"
include "coeq1d.mm"
include "simprd.mm"
include "evlf1.mm"
include "fcompt.mm"
include "fveq2.mm"
include "3eqtr4d.mm"

theorem yonedalem3b
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.1: class .1.
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
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
  let vv: setvar v
  let cN: class N
  let cI: class I
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
  assume yonedalem22.g: |- ( ph -> G e. ( O Func S ) )
  assume yonedalem22.p: |- ( ph -> P e. B )
  assume yonedalem22.a: |- ( ph -> A e. ( F ( O Nat S ) G ) )
  assume yonedalem22.k: |- ( ph -> K e. ( P ( Hom ` C ) X ) )
  assume yonedalem3.m: |- M = ( f e. ( O Func S ) , x e. B |-> ( a e. ( ( ( 1st ` Y ) ` x ) ( O Nat S ) f ) |-> ( ( a ` x ) ` ( .1. ` x ) ) ) )

  disjoint a f
  disjoint a x
  disjoint .1. a
  disjoint f x
  disjoint .1. f
  disjoint .1. x
  disjoint A a
  disjoint C a
  disjoint C f
  disjoint C x
  disjoint E a
  disjoint E f
  disjoint F a
  disjoint F f
  disjoint F x
  disjoint K a
  disjoint B a
  disjoint B f
  disjoint B x
  disjoint G a
  disjoint G f
  disjoint G x
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
  disjoint P a
  disjoint P f
  disjoint P x
  disjoint a ph
  disjoint f ph
  disjoint ph x
  disjoint Y a
  disjoint Y f
  disjoint Y x
  disjoint Z a
  disjoint Z f
  disjoint Z x
  disjoint X a
  disjoint X f
  disjoint X x
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
  disjoint F b
  disjoint F g
  disjoint F h
  disjoint k x
  disjoint F k
  disjoint F u
  disjoint F w
  disjoint F y
  disjoint F z
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
  disjoint G b
  disjoint G g
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
  disjoint P b
  disjoint P g
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
  disjoint X b
  disjoint X g
  disjoint X h
  disjoint X k
  disjoint X u
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( ( G M P ) ( <. ( F ( 1st ` Z ) X ) , ( G ( 1st ` Z ) P ) >. ( comp ` T ) ( G ( 1st ` E ) P ) ) ( A ( <. F , X >. ( 2nd ` Z ) <. G , P >. ) K ) ) = ( ( A ( <. F , X >. ( 2nd ` E ) <. G , P >. ) K ) ( <. ( F ( 1st ` Z ) X ) , ( F ( 1st ` E ) X ) >. ( comp ` T ) ( G ( 1st ` E ) P ) ) ( F M X ) ) )

  proof
    wph
    cG
    cP
    cM
    co
    #
    cA
    cK
    cF
    cX
    cop
    #
    cG
    cP
    cop
    #
    cZ
    c2nd
    cfv
    #
    co
    #
    co
    #
    ccom
    #
    cA
    cK
    @1
    @2
    cE
    c2nd
    cfv
    #
    co
    #
    co
    #
    cF
    cX
    cM
    co
    #
    ccom
    #
    @0
    @5
    cF
    cX
    cZ
    c1st
    cfv
    #
    co
    #
    cG
    cP
    @12
    co
    #
    cop
    cG
    cP
    cE
    c1st
    cfv
    #
    co
    #
    cT
    cco
    cfv
    #
    co
    co
    @9
    @10
    @13
    cF
    cX
    @15
    co
    #
    cop
    @16
    @17
    co
    co
    wph
    vb
    cX
    cY
    c1st
    cfv
    #
    cfv
    #
    cF
    cO
    cS
    cnat
    co
    #
    co
    #
    cP
    c.1
    cfv
    #
    cP
    cA
    vb
    cv
    #
    @20
    cF
    cop
    #
    cG
    cQ
    cco
    cfv
    #
    co
    #
    co
    #
    cK
    cP
    cX
    cY
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cP
    @19
    cfv
    #
    @20
    cop
    cG
    @26
    co
    #
    co
    #
    cfv
    #
    cfv
    #
    cmpt
    #
    va
    @22
    cX
    c.1
    cfv
    #
    cX
    va
    cv
    #
    cfv
    #
    cfv
    #
    cK
    cX
    cP
    cF
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cfv
    #
    cP
    cA
    cfv
    #
    cfv
    #
    cmpt
    #
    @6
    @11
    wph
    @37
    va
    @22
    @23
    cP
    cA
    @39
    @27
    co
    #
    @31
    @33
    co
    #
    cfv
    #
    cfv
    #
    cmpt
    @48
    vb
    va
    @22
    @36
    @52
    @24
    @39
    wceq
    #
    @23
    @35
    @51
    @53
    cP
    @34
    @50
    @53
    @28
    @49
    @31
    @33
    @24
    @39
    cA
    @27
    oveq2
    oveq1d
    fveq1d
    fveq1d
    cbvmptv
    wph
    va
    @22
    @52
    @47
    wph
    @39
    @22
    wcel
    #
    wa
    #
    @52
    @23
    @46
    cP
    @39
    cfv
    #
    ccom
    #
    cP
    @31
    cfv
    #
    ccom
    #
    cfv
    #
    @23
    @58
    cfv
    #
    @57
    cfv
    #
    @47
    @55
    @23
    @51
    @59
    @55
    @51
    cP
    @49
    cfv
    #
    @58
    cP
    @32
    c1st
    cfv
    #
    cfv
    #
    cP
    @20
    c1st
    cfv
    #
    cfv
    #
    cop
    cP
    cG
    c1st
    cfv
    #
    cfv
    #
    cS
    cco
    cfv
    #
    co
    #
    co
    @57
    @58
    @71
    co
    @59
    @55
    cB
    cO
    cS
    cQ
    @31
    @49
    @26
    @70
    @32
    @20
    cG
    @21
    cP
    yoneda.q
    @21
    eqid
    #
    cB
    cC
    cO
    yoneda.o
    yoneda.b
    oppcbas
    #
    @70
    eqid
    #
    @26
    eqid
    #
    wph
    @31
    @32
    @20
    @21
    co
    #
    wcel
    @54
    wph
    cP
    cX
    cC
    chom
    cfv
    #
    co
    #
    @76
    cK
    @30
    wph
    cB
    cC
    cQ
    @19
    @29
    @77
    @21
    cP
    cX
    yoneda.b
    @77
    eqid
    #
    cO
    cS
    cQ
    @21
    yoneda.q
    @72
    fuchom
    #
    wph
    cC
    cQ
    cfunc
    co
    #
    wrel
    cY
    @81
    wcel
    @19
    @29
    @81
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
    cU
    cV
    yoneda.v
    unssbd
    ssexd
    #
    yoneda.u
    yoncl
    cY
    @81
    1st2ndbr
    sylancr
    #
    yonedalem22.p
    yonedalem21.x
    funcf2
    yonedalem22.k
    ffvelrnd
    #
    adantr
    @55
    cO
    cS
    cQ
    @39
    cA
    @26
    @20
    cF
    cG
    @21
    yoneda.q
    @72
    @75
    wph
    @54
    simpr
    #
    wph
    cA
    cF
    cG
    @21
    co
    #
    wcel
    @54
    yonedalem22.a
    adantr
    #
    fuccocl
    wph
    cP
    cB
    wcel
    #
    @54
    yonedalem22.p
    adantr
    #
    fuccoval
    @55
    @63
    @57
    @58
    @71
    @55
    @63
    @46
    @56
    @67
    cP
    cF
    c1st
    cfv
    #
    cfv
    #
    cop
    @69
    @70
    co
    co
    @57
    @55
    cB
    cO
    cS
    cQ
    @39
    cA
    @26
    @70
    @20
    cF
    cG
    @21
    cP
    yoneda.q
    @72
    @73
    @74
    @75
    @85
    @87
    @89
    fuccoval
    @55
    cS
    @70
    cU
    @56
    @46
    cvv
    @67
    @91
    @69
    yoneda.s
    wph
    cU
    cvv
    wcel
    #
    @54
    @82
    adantr
    #
    @74
    wph
    @67
    cU
    wcel
    @54
    wph
    cB
    cU
    cP
    @66
    wph
    cB
    cU
    @66
    wf
    cB
    cS
    cbs
    cfv
    #
    @66
    wf
    wph
    cB
    @94
    cO
    cS
    @66
    @20
    c2nd
    cfv
    #
    @73
    @94
    eqid
    #
    wph
    cO
    cS
    cfunc
    co
    #
    wrel
    #
    @20
    @97
    wcel
    @66
    @95
    @97
    wbr
    cO
    cS
    relfunc
    #
    wph
    cB
    @97
    cX
    @19
    wph
    cB
    @97
    cC
    cQ
    @19
    @29
    yoneda.b
    cO
    cS
    cQ
    yoneda.q
    fucbas
    #
    @83
    funcf1
    #
    yonedalem21.x
    ffvelrnd
    #
    @20
    @97
    1st2ndbr
    sylancr
    #
    funcf1
    wph
    cU
    @94
    @66
    cB
    wph
    cS
    cU
    cvv
    yoneda.s
    @82
    setcbas
    #
    feq3d
    mpbird
    #
    yonedalem22.p
    ffvelrnd
    #
    adantr
    #
    wph
    @91
    cU
    wcel
    @54
    wph
    cB
    cU
    cP
    @90
    wph
    cB
    cU
    @90
    wf
    cB
    @94
    @90
    wf
    wph
    cB
    @94
    cO
    cS
    @90
    @42
    @73
    @96
    wph
    @98
    cF
    @97
    wcel
    #
    @90
    @42
    @97
    wbr
    @99
    yonedalem21.f
    cF
    @97
    1st2ndbr
    sylancr
    #
    funcf1
    wph
    cU
    @94
    @90
    cB
    @104
    feq3d
    mpbird
    #
    yonedalem22.p
    ffvelrnd
    #
    adantr
    #
    wph
    @69
    cU
    wcel
    @54
    wph
    @69
    @94
    cU
    wph
    cB
    @94
    cP
    @68
    wph
    cB
    @94
    cO
    cS
    @68
    cG
    c2nd
    cfv
    #
    @73
    @96
    wph
    @98
    cG
    @97
    wcel
    #
    @68
    @113
    @97
    wbr
    @99
    yonedalem22.g
    cG
    @97
    1st2ndbr
    sylancr
    funcf1
    yonedalem22.p
    ffvelrnd
    @104
    eleqtrrd
    #
    adantr
    #
    @55
    @56
    @67
    @91
    cS
    chom
    cfv
    #
    co
    wcel
    @67
    @91
    @56
    wf
    #
    @55
    @39
    cB
    cO
    cS
    @66
    @95
    @117
    @90
    @42
    @21
    cP
    @72
    @55
    @39
    cO
    cS
    @20
    cF
    @21
    @72
    @85
    nat1st2nd
    #
    @73
    @117
    eqid
    #
    @89
    natcl
    @55
    cS
    cU
    @56
    @117
    cvv
    @67
    @91
    yoneda.s
    @93
    @120
    @107
    @112
    elsetchom
    mpbid
    #
    wph
    @91
    @69
    @46
    wf
    #
    @54
    wph
    @46
    @91
    @69
    @117
    co
    wcel
    @122
    wph
    cA
    cB
    cO
    cS
    @90
    @42
    @117
    @68
    @113
    @21
    cP
    @72
    wph
    cA
    cO
    cS
    cF
    cG
    @21
    @72
    yonedalem22.a
    nat1st2nd
    @73
    @120
    yonedalem22.p
    natcl
    wph
    cS
    cU
    @46
    @117
    cvv
    @91
    @69
    yoneda.s
    @82
    @120
    @111
    @115
    elsetchom
    mpbid
    #
    adantr
    #
    setcco
    eqtrd
    oveq1d
    @55
    cS
    @70
    cU
    @58
    @57
    cvv
    @65
    @67
    @69
    yoneda.s
    @93
    @74
    wph
    @65
    cU
    wcel
    @54
    wph
    @65
    @94
    cU
    wph
    cB
    @94
    cP
    @64
    wph
    cB
    @94
    cO
    cS
    @64
    @32
    c2nd
    cfv
    #
    @73
    @96
    wph
    @98
    @32
    @97
    wcel
    @64
    @125
    @97
    wbr
    @99
    wph
    cB
    @97
    cP
    @19
    @101
    yonedalem22.p
    ffvelrnd
    #
    @32
    @97
    1st2ndbr
    sylancr
    funcf1
    yonedalem22.p
    ffvelrnd
    @104
    eleqtrrd
    #
    adantr
    @107
    @116
    wph
    @65
    @67
    @58
    wf
    #
    @54
    wph
    @58
    @65
    @67
    @117
    co
    wcel
    @128
    wph
    @31
    cB
    cO
    cS
    @64
    @125
    @117
    @66
    @95
    @21
    cP
    @72
    wph
    @31
    cO
    cS
    @32
    @20
    @21
    @72
    @84
    nat1st2nd
    @73
    @120
    yonedalem22.p
    natcl
    wph
    cS
    cU
    @58
    @117
    cvv
    @65
    @67
    yoneda.s
    @82
    @120
    @127
    @106
    elsetchom
    mpbid
    adantr
    #
    @55
    @122
    @118
    @67
    @69
    @57
    wf
    @124
    @121
    @67
    @91
    @69
    @46
    @56
    fco
    syl2anc
    setcco
    3eqtrd
    fveq1d
    @55
    @128
    @23
    @65
    wcel
    #
    @60
    @62
    wceq
    @129
    wph
    @130
    @54
    wph
    @23
    cP
    cP
    @77
    co
    #
    @65
    wph
    cB
    cC
    c.1
    @77
    cP
    yoneda.b
    @79
    yoneda.1
    yoneda.c
    yonedalem22.p
    catidcl
    #
    wph
    cB
    cC
    @77
    cP
    cY
    cP
    yoneda.y
    yoneda.b
    yoneda.c
    yonedalem22.p
    @79
    yonedalem22.p
    yon11
    eleqtrrd
    adantr
    #
    @65
    @67
    @23
    @57
    @58
    fvco3
    syl2anc
    @55
    @62
    @61
    @56
    cfv
    #
    @46
    cfv
    #
    @47
    @55
    @118
    @61
    @67
    wcel
    @62
    @135
    wceq
    @121
    @55
    @65
    @67
    @23
    @58
    @129
    @133
    ffvelrnd
    @67
    @91
    @61
    @46
    @56
    fvco3
    syl2anc
    @55
    @134
    @45
    @46
    @55
    @134
    cK
    @56
    cfv
    #
    @38
    @44
    @40
    ccom
    #
    cfv
    #
    @45
    @55
    @61
    cK
    @56
    @55
    @61
    cK
    @23
    cP
    cP
    cop
    cX
    cC
    cco
    cfv
    #
    co
    co
    cK
    @55
    cB
    cC
    @139
    cK
    @23
    @77
    cP
    cP
    cY
    cX
    yoneda.y
    yoneda.b
    wph
    cC
    ccat
    wcel
    #
    @54
    yoneda.c
    adantr
    #
    @89
    @79
    wph
    cX
    cB
    wcel
    #
    @54
    yonedalem21.x
    adantr
    #
    @139
    eqid
    #
    @89
    wph
    cK
    @78
    wcel
    @54
    yonedalem22.k
    adantr
    #
    wph
    @23
    @131
    wcel
    @54
    @132
    adantr
    yon2
    @55
    cB
    cC
    @139
    c.1
    cK
    @77
    cP
    cX
    yoneda.b
    @79
    yoneda.1
    @141
    @89
    @144
    @143
    @145
    catrid
    eqtrd
    fveq2d
    @55
    @38
    @56
    cK
    cX
    cP
    @95
    co
    #
    cfv
    #
    ccom
    #
    cfv
    #
    @38
    @147
    cfv
    #
    @56
    cfv
    #
    @138
    @136
    @55
    cX
    @66
    cfv
    #
    @67
    @147
    wf
    #
    @38
    @152
    wcel
    #
    @149
    @151
    wceq
    wph
    @153
    @54
    wph
    @147
    @152
    @67
    @117
    co
    #
    wcel
    @153
    wph
    cX
    cP
    cO
    chom
    cfv
    #
    co
    #
    @155
    cK
    @146
    wph
    cB
    cO
    cS
    @66
    @95
    @156
    @117
    cX
    cP
    @73
    @156
    eqid
    #
    @120
    @103
    yonedalem21.x
    yonedalem22.p
    funcf2
    wph
    cK
    @78
    @157
    yonedalem22.k
    cC
    @77
    cO
    cX
    cP
    @79
    yoneda.o
    oppchom
    #
    syl6eleqr
    #
    ffvelrnd
    wph
    cS
    cU
    @147
    @117
    cvv
    @152
    @67
    yoneda.s
    @82
    @120
    wph
    cB
    cU
    cX
    @66
    @105
    yonedalem21.x
    ffvelrnd
    #
    @106
    elsetchom
    mpbid
    adantr
    #
    wph
    @154
    @54
    wph
    @38
    cX
    cX
    @77
    co
    #
    @152
    wph
    cB
    cC
    c.1
    @77
    cX
    yoneda.b
    @79
    yoneda.1
    yoneda.c
    yonedalem21.x
    catidcl
    #
    wph
    cB
    cC
    @77
    cX
    cY
    cX
    yoneda.y
    yoneda.b
    yoneda.c
    yonedalem21.x
    @79
    yonedalem21.x
    yon11
    eleqtrrd
    adantr
    #
    @152
    @67
    @38
    @56
    @147
    fvco3
    syl2anc
    @55
    @38
    @148
    @137
    @55
    @56
    @147
    @152
    @67
    cop
    @91
    @70
    co
    co
    @44
    @40
    @152
    cX
    @90
    cfv
    #
    cop
    @91
    @70
    co
    co
    @148
    @137
    @55
    @39
    cB
    cO
    cS
    cK
    @70
    @66
    @95
    @156
    @90
    @42
    @21
    cX
    cP
    @72
    @119
    @73
    @158
    @74
    @143
    @89
    wph
    cK
    @157
    wcel
    @54
    @160
    adantr
    nati
    @55
    cS
    @70
    cU
    @147
    @56
    cvv
    @152
    @67
    @91
    yoneda.s
    @93
    @74
    wph
    @152
    cU
    wcel
    @54
    @161
    adantr
    #
    @107
    @112
    @162
    @121
    setcco
    @55
    cS
    @70
    cU
    @40
    @44
    cvv
    @152
    @166
    @91
    yoneda.s
    @93
    @74
    @167
    wph
    @166
    cU
    wcel
    @54
    wph
    cB
    cU
    cX
    @90
    @110
    yonedalem21.x
    ffvelrnd
    #
    adantr
    #
    @112
    @55
    @40
    @152
    @166
    @117
    co
    wcel
    @152
    @166
    @40
    wf
    #
    @55
    @39
    cB
    cO
    cS
    @66
    @95
    @117
    @90
    @42
    @21
    cX
    @72
    @119
    @73
    @120
    @143
    natcl
    @55
    cS
    cU
    @40
    @117
    cvv
    @152
    @166
    yoneda.s
    @93
    @120
    @167
    @169
    elsetchom
    mpbid
    #
    wph
    @166
    @91
    @44
    wf
    #
    @54
    wph
    @44
    @166
    @91
    @117
    co
    #
    wcel
    @172
    wph
    @157
    @173
    cK
    @43
    wph
    cB
    cO
    cS
    @90
    @42
    @156
    @117
    cX
    cP
    @73
    @158
    @120
    @109
    yonedalem21.x
    yonedalem22.p
    funcf2
    @160
    ffvelrnd
    wph
    cS
    cU
    @44
    @117
    cvv
    @166
    @91
    yoneda.s
    @82
    @120
    @168
    @111
    elsetchom
    mpbid
    #
    adantr
    setcco
    3eqtr3d
    fveq1d
    @55
    @150
    cK
    @56
    @55
    @150
    @38
    cK
    cP
    cX
    cop
    cX
    @139
    co
    co
    cK
    @55
    cB
    cC
    @139
    cK
    @38
    @77
    cP
    cX
    cY
    cX
    yoneda.y
    yoneda.b
    @141
    @143
    @79
    @143
    @144
    @89
    @145
    wph
    @38
    @163
    wcel
    @54
    @164
    adantr
    yon12
    @55
    cB
    cC
    @139
    c.1
    cK
    @77
    cP
    cX
    yoneda.b
    @79
    yoneda.1
    @141
    @89
    @144
    @143
    @145
    catlid
    eqtrd
    fveq2d
    3eqtr3d
    @55
    @170
    @154
    @138
    @45
    wceq
    @171
    @165
    @152
    @166
    @38
    @44
    @40
    fvco3
    syl2anc
    3eqtr2d
    fveq2d
    eqtrd
    3eqtrd
    mpteq2dva
    syl5eq
    wph
    vb
    va
    @22
    @32
    cG
    @21
    co
    #
    @34
    @23
    @56
    cfv
    #
    @36
    @5
    @0
    wph
    @22
    @175
    vb
    @22
    @34
    cmpt
    #
    wf
    #
    @34
    @175
    wcel
    vb
    @22
    wral
    wph
    @13
    @14
    @5
    wf
    #
    @178
    wph
    @5
    @13
    @14
    cT
    chom
    cfv
    #
    co
    #
    wcel
    @179
    wph
    cA
    cK
    @181
    @86
    @78
    @4
    wph
    @1
    @2
    cQ
    cO
    cxpc
    co
    #
    chom
    cfv
    #
    co
    #
    @1
    @12
    cfv
    #
    @2
    @12
    cfv
    #
    @180
    co
    #
    @4
    wf
    @86
    @78
    cxp
    #
    @181
    @4
    wf
    wph
    @97
    cB
    cxp
    #
    @182
    cT
    @12
    @3
    @183
    @180
    @1
    @2
    cQ
    cO
    @182
    @97
    cB
    @182
    eqid
    #
    @100
    @73
    xpcbas
    #
    @183
    eqid
    #
    @180
    eqid
    #
    wph
    @182
    cT
    cfunc
    co
    #
    wrel
    #
    cZ
    @194
    wcel
    #
    @12
    @3
    @194
    wbr
    @182
    cT
    relfunc
    #
    wph
    @196
    cE
    @194
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
    cZ
    @194
    1st2ndbr
    sylancr
    #
    wph
    @108
    @142
    @1
    @189
    wcel
    yonedalem21.f
    yonedalem21.x
    cF
    cX
    @97
    cB
    opelxpi
    syl2anc
    #
    wph
    @114
    @88
    @2
    @189
    wcel
    yonedalem22.g
    yonedalem22.p
    cG
    cP
    @97
    cB
    opelxpi
    syl2anc
    #
    funcf2
    wph
    @184
    @187
    @188
    @181
    @4
    wph
    @184
    @86
    @157
    cxp
    @188
    wph
    cQ
    cO
    cG
    cP
    @182
    @21
    @156
    @183
    cF
    cX
    @97
    cB
    @190
    @100
    @73
    @80
    @158
    yonedalem21.f
    yonedalem21.x
    yonedalem22.g
    yonedalem22.p
    @192
    xpchom2
    @157
    @78
    @86
    @159
    xpeq2i
    syl6eq
    #
    @187
    @181
    wceq
    wph
    @181
    @187
    @13
    @185
    @14
    @186
    @180
    cF
    cX
    @12
    df-ov
    cG
    cP
    @12
    df-ov
    oveq12i
    eqcomi
    a1i
    feq23d
    mpbid
    yonedalem22.a
    yonedalem22.k
    fovrnd
    wph
    cT
    cV
    @5
    @180
    cW
    @13
    @14
    yoneda.t
    yoneda.w
    @193
    wph
    @13
    cT
    cbs
    cfv
    #
    cV
    wph
    cF
    cX
    @204
    @97
    cB
    @12
    wph
    @189
    @204
    @182
    cT
    @12
    @3
    @191
    @204
    eqid
    #
    @200
    funcf1
    #
    yonedalem21.f
    yonedalem21.x
    fovrnd
    wph
    cT
    cV
    cW
    yoneda.t
    yoneda.w
    setcbas
    #
    eleqtrrd
    #
    wph
    @14
    @204
    cV
    wph
    cG
    cP
    @204
    @97
    cB
    @12
    @206
    yonedalem22.g
    yonedalem22.p
    fovrnd
    @207
    eleqtrrd
    #
    elsetchom
    mpbid
    #
    wph
    @13
    @22
    @14
    @175
    @5
    @177
    wph
    @5
    @31
    cA
    @25
    @32
    cG
    cop
    cH
    c2nd
    cfv
    co
    co
    @177
    wph
    cA
    cB
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.1
    cE
    cF
    cG
    cH
    cK
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
    yonedalem22.g
    yonedalem22.p
    yonedalem22.a
    yonedalem22.k
    yonedalem22
    wph
    @97
    cQ
    @26
    vb
    @31
    cA
    @21
    cH
    cG
    @20
    cF
    @32
    yoneda.h
    wph
    cO
    cS
    cQ
    yoneda.q
    wph
    @140
    cO
    ccat
    wcel
    yoneda.c
    cC
    cO
    yoneda.o
    oppccat
    syl
    #
    wph
    @92
    cS
    ccat
    wcel
    @82
    cS
    cU
    cvv
    yoneda.s
    setccat
    syl
    #
    fuccat
    @100
    @80
    @102
    yonedalem21.f
    @126
    yonedalem22.g
    @75
    @84
    yonedalem22.a
    hof2val
    eqtrd
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
    cF
    cH
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
    yonedalem21
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
    cG
    cH
    cO
    cV
    cW
    cP
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
    yonedalem22.g
    yonedalem22.p
    yonedalem21
    feq123d
    mpbid
    vb
    @22
    @175
    @34
    @177
    @177
    eqid
    fmpt
    sylibr
    @213
    wph
    @0
    va
    @175
    @176
    cmpt
    wceq
    #
    @14
    @16
    @0
    wf
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
    cG
    cH
    cM
    cO
    cV
    cW
    cP
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
    yonedalem22.g
    yonedalem22.p
    yonedalem3.m
    yonedalem3a
    #
    simpld
    @39
    @34
    wceq
    @23
    @56
    @35
    cP
    @39
    @34
    fveq1
    fveq1d
    fmptcof
    wph
    @11
    @46
    @44
    ccom
    #
    @10
    ccom
    @48
    wph
    @9
    @218
    @10
    wph
    @9
    @46
    @44
    @166
    @91
    cop
    @69
    @70
    co
    co
    @218
    wph
    cA
    cB
    cO
    cS
    @70
    cE
    cF
    cG
    @156
    cK
    @8
    @21
    cX
    cP
    yoneda.e
    @211
    @212
    @73
    @158
    @74
    @72
    yonedalem21.f
    yonedalem22.g
    yonedalem21.x
    yonedalem22.p
    @8
    eqid
    yonedalem22.a
    @160
    evlf2val
    wph
    cS
    @70
    cU
    @44
    @46
    cvv
    @166
    @91
    @69
    yoneda.s
    @82
    @74
    @168
    @111
    @115
    @174
    @123
    setcco
    eqtrd
    coeq1d
    wph
    va
    vy
    @22
    @166
    @41
    vy
    cv
    #
    @44
    cfv
    #
    @46
    cfv
    #
    @47
    @10
    @218
    wph
    @22
    @166
    va
    @22
    @41
    cmpt
    #
    wf
    #
    @41
    @166
    wcel
    va
    @22
    wral
    wph
    @13
    @18
    @10
    wf
    #
    @223
    wph
    @10
    @222
    wceq
    #
    @224
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
    cF
    cH
    cM
    cO
    cV
    cW
    cX
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
    yonedalem21.f
    yonedalem21.x
    yonedalem3.m
    yonedalem3a
    #
    simprd
    #
    wph
    @13
    @22
    @18
    @166
    @10
    @222
    wph
    @225
    @224
    @226
    simpld
    #
    @214
    wph
    cB
    cO
    cS
    cE
    cF
    cX
    yoneda.e
    @211
    @212
    @73
    yonedalem21.f
    yonedalem21.x
    evlf1
    feq123d
    mpbid
    va
    @22
    @166
    @41
    @222
    @222
    eqid
    fmpt
    sylibr
    @228
    wph
    @122
    @172
    @218
    vy
    @166
    @221
    cmpt
    wceq
    @123
    @174
    vy
    @46
    @44
    @166
    @91
    @69
    fcompt
    syl2anc
    @219
    @41
    wceq
    @220
    @45
    @46
    @219
    @41
    @44
    fveq2
    fveq2d
    fmptcof
    eqtrd
    3eqtr4d
    wph
    cT
    @17
    cV
    @5
    @0
    cW
    @13
    @14
    @16
    yoneda.t
    yoneda.w
    @17
    eqid
    #
    @208
    @209
    wph
    @16
    @204
    cV
    wph
    cG
    cP
    @204
    @97
    cB
    @15
    wph
    @189
    @204
    @182
    cT
    @15
    @7
    @191
    @205
    wph
    @195
    @198
    @15
    @7
    @194
    wbr
    @197
    wph
    @196
    @198
    @199
    simprd
    cE
    @194
    1st2ndbr
    sylancr
    #
    funcf1
    #
    yonedalem22.g
    yonedalem22.p
    fovrnd
    @207
    eleqtrrd
    #
    @210
    wph
    @215
    @216
    @217
    simprd
    setcco
    wph
    cT
    @17
    cV
    @10
    @9
    cW
    @13
    @18
    @16
    yoneda.t
    yoneda.w
    @229
    @208
    wph
    @18
    @204
    cV
    wph
    cF
    cX
    @204
    @97
    cB
    @15
    @231
    yonedalem21.f
    yonedalem21.x
    fovrnd
    @207
    eleqtrrd
    #
    @232
    @227
    wph
    @9
    @18
    @16
    @180
    co
    #
    wcel
    @18
    @16
    @9
    wf
    wph
    cA
    cK
    @234
    @86
    @78
    @8
    wph
    @184
    @1
    @15
    cfv
    #
    @2
    @15
    cfv
    #
    @180
    co
    #
    @8
    wf
    @188
    @234
    @8
    wf
    wph
    @189
    @182
    cT
    @15
    @7
    @183
    @180
    @1
    @2
    @191
    @192
    @193
    @230
    @201
    @202
    funcf2
    wph
    @184
    @237
    @188
    @234
    @8
    @203
    @237
    @234
    wceq
    wph
    @234
    @237
    @18
    @235
    @16
    @236
    @180
    cF
    cX
    @15
    df-ov
    cG
    cP
    @15
    df-ov
    oveq12i
    eqcomi
    a1i
    feq23d
    mpbid
    yonedalem22.a
    yonedalem22.k
    fovrnd
    wph
    cT
    cV
    @9
    @180
    cW
    @18
    @16
    yoneda.t
    yoneda.w
    @193
    @233
    @232
    elsetchom
    mpbid
    setcco
    3eqtr4d
end
