include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cful.mm"
include "co.mm"
include "cfth.mm"
include "cin.mm"
include "cfunc.mm"
include "wrel.mm"
include "wcel.mm"
include "wceq.mm"
include "relfunc.mm"
include "cvv.mm"
include "chomf.mm"
include "crn.mm"
include "unssbd.mm"
include "ssexd.mm"
include "yoncl.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "wbr.mm"
include "cv.mm"
include "chom.mm"
include "cnat.mm"
include "wf1o.mm"
include "wral.mm"
include "1st2ndbr.mm"
include "wa.mm"
include "ciso.mm"
include "cxp.mm"
include "wf.mm"
include "fucbas.mm"
include "funcf1.mm"
include "adantr.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "simprl.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "cxpc.mm"
include "ccat.mm"
include "yonedalem1.mm"
include "simpld.mm"
include "funcrcl.mm"
include "syl.mm"
include "simprd.mm"
include "fuccat.mm"
include "eqid.mm"
include "yonedainv.mm"
include "inviso2.mm"
include "oppcbas.mm"
include "xpcbas.mm"
include "fuciso.mm"
include "mpbid.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "oppccat.mm"
include "setccat.mm"
include "evlf1.mm"
include "yon11.mm"
include "eqtrd.mm"
include "wss.mm"
include "cun.mm"
include "yonedalem21.mm"
include "eleqtrd.mm"
include "cbs.mm"
include "setcbas.mm"
include "eleqtrrd.mm"
include "eqeltrrd.mm"
include "sseldd.mm"
include "fuchom.mm"
include "homfval.mm"
include "unssad.mm"
include "wfn.mm"
include "homffn.mm"
include "a1i.mm"
include "fnovrn.mm"
include "syl3anc.mm"
include "setciso.mm"
include "wb.mm"
include "cmpt.mm"
include "simpr.mm"
include "eqcomd.mm"
include "cco.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "yon12.mm"
include "yon2.mm"
include "eqtr4d.mm"
include "mpteq12dva.mm"
include "funcf2.mm"
include "ffvelrnda.mm"
include "nat1st2nd.mm"
include "natcl.mm"
include "ad2antrr.mm"
include "elsetchom.mm"
include "feqmptd.mm"
include "mpteq2dva.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "yonedalem4a.mm"
include "natfn.mm"
include "dffn5.mm"
include "sylib.mm"
include "3eqtr4d.mm"
include "f1of.mm"
include "f1oeq1.mm"
include "ralrimivva.mm"
include "isffth2.mm"
include "sylanbrc.mm"
include "df-br.mm"
include "eqeltrd.mm"

theorem yonffthlem
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
  assert |- ( ph -> Y e. ( ( C Full Q ) i^i ( C Faith Q ) ) )

  proof
    wph
    cY
    cY
    c1st
    cfv
    #
    cY
    c2nd
    cfv
    #
    cop
    #
    cC
    cQ
    cful
    co
    cC
    cQ
    cfth
    co
    cin
    #
    wph
    cC
    cQ
    cfunc
    co
    #
    wrel
    #
    cY
    @4
    wcel
    #
    cY
    @2
    wceq
    cC
    cQ
    relfunc
    #
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
    #
    crn
    #
    cU
    cV
    yoneda.v
    unssbd
    #
    ssexd
    #
    yoneda.u
    yoncl
    #
    cY
    @4
    1st2nd
    sylancr
    wph
    @0
    @1
    @3
    wbr
    #
    @2
    @3
    wcel
    wph
    @0
    @1
    @4
    wbr
    #
    vz
    cv
    #
    vw
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    @15
    @0
    cfv
    #
    @16
    @0
    cfv
    #
    cO
    cS
    cnat
    co
    #
    co
    #
    @15
    @16
    @1
    co
    #
    wf1o
    #
    vw
    cB
    wral
    vz
    cB
    wral
    @13
    wph
    @5
    @6
    @14
    @7
    @12
    cY
    @4
    1st2ndbr
    sylancr
    #
    wph
    @24
    vz
    vw
    cB
    cB
    wph
    @15
    cB
    wcel
    #
    @16
    cB
    wcel
    #
    wa
    #
    wa
    #
    @18
    @22
    @20
    @15
    cN
    co
    #
    wf1o
    #
    @24
    @29
    @30
    @18
    @22
    cT
    ciso
    cfv
    #
    co
    #
    wcel
    @31
    @29
    @30
    @20
    @15
    cE
    c1st
    cfv
    #
    co
    #
    @20
    @15
    cZ
    c1st
    cfv
    #
    co
    #
    @32
    co
    #
    @33
    @29
    @20
    @15
    cop
    #
    cO
    cS
    cfunc
    co
    #
    cB
    cxp
    #
    wcel
    #
    vv
    cv
    #
    cN
    cfv
    #
    @43
    @34
    cfv
    #
    @43
    @36
    cfv
    #
    @32
    co
    #
    wcel
    #
    vv
    @41
    wral
    #
    @30
    @38
    wcel
    #
    @29
    @20
    @40
    wcel
    #
    @26
    @42
    @29
    cB
    @40
    @16
    @0
    wph
    cB
    @40
    @0
    wf
    #
    @28
    wph
    cB
    @40
    cC
    cQ
    @0
    @1
    yoneda.b
    cO
    cS
    cQ
    yoneda.q
    fucbas
    #
    @25
    funcf1
    #
    adantr
    #
    wph
    @26
    @27
    simprr
    #
    ffvelrnd
    #
    wph
    @26
    @27
    simprl
    #
    @20
    @15
    @40
    cB
    opelxpi
    syl2anc
    wph
    @49
    @28
    wph
    cN
    cE
    cZ
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
    #
    @49
    wph
    cN
    cE
    cZ
    cR
    ciso
    cfv
    #
    co
    wcel
    @61
    @49
    wa
    wph
    @59
    cT
    cfunc
    co
    #
    cR
    cM
    cN
    @62
    cI
    cZ
    cE
    @59
    cT
    cR
    yoneda.r
    fucbas
    yonedainv.i
    wph
    @59
    cT
    cR
    yoneda.r
    wph
    @59
    ccat
    wcel
    #
    cT
    ccat
    wcel
    #
    wph
    cZ
    @63
    wcel
    #
    @64
    @65
    wa
    wph
    @66
    cE
    @63
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
    @59
    cT
    cZ
    funcrcl
    syl
    #
    simpld
    wph
    @64
    @65
    @70
    simprd
    fuccat
    @69
    wph
    @66
    @67
    @68
    simprd
    #
    @62
    eqid
    #
    wph
    vx
    vy
    vu
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
    cH
    cI
    cM
    cN
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
    yonedainv.i
    yonedainv.n
    yonedainv
    inviso2
    wph
    vv
    cN
    @41
    @59
    cT
    cR
    cE
    cZ
    @62
    @32
    @60
    yoneda.r
    cQ
    cO
    @59
    @40
    cB
    @59
    eqid
    @53
    cB
    cC
    cO
    yoneda.o
    yoneda.b
    oppcbas
    #
    xpcbas
    @60
    eqid
    @71
    @69
    @72
    @32
    eqid
    #
    fuciso
    mpbid
    simprd
    adantr
    @48
    @50
    vv
    @39
    @41
    @43
    @39
    wceq
    #
    @44
    @30
    @47
    @38
    @75
    @44
    @39
    cN
    cfv
    @30
    @43
    @39
    cN
    fveq2
    @20
    @15
    cN
    df-ov
    syl6eqr
    @75
    @45
    @35
    @46
    @37
    @32
    @75
    @45
    @39
    @34
    cfv
    @35
    @43
    @39
    @34
    fveq2
    @20
    @15
    @34
    df-ov
    syl6eqr
    @75
    @46
    @39
    @36
    cfv
    @37
    @43
    @39
    @36
    fveq2
    @20
    @15
    @36
    df-ov
    syl6eqr
    oveq12d
    eleq12d
    rspcv
    sylc
    @29
    @35
    @18
    @37
    @22
    @32
    @29
    @35
    @15
    @20
    c1st
    cfv
    #
    cfv
    #
    @18
    @29
    cB
    cO
    cS
    cE
    @20
    @15
    yoneda.e
    wph
    cO
    ccat
    wcel
    #
    @28
    wph
    cC
    ccat
    wcel
    #
    @78
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
    @28
    wph
    cU
    cvv
    wcel
    #
    @80
    @11
    cS
    cU
    cvv
    yoneda.s
    setccat
    syl
    adantr
    @73
    @57
    @58
    evlf1
    @29
    cB
    cC
    @17
    @16
    cY
    @15
    yoneda.y
    yoneda.b
    wph
    @79
    @28
    yoneda.c
    adantr
    #
    @56
    @17
    eqid
    #
    @58
    yon11
    #
    eqtrd
    @29
    cB
    cC
    cQ
    cR
    cS
    cT
    cU
    c.1
    cE
    @20
    cH
    cO
    cV
    cW
    @15
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
    @82
    wph
    cV
    cW
    wcel
    #
    @28
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
    @28
    yoneda.u
    adantr
    #
    wph
    @9
    cU
    cun
    cV
    wss
    #
    @28
    yoneda.v
    adantr
    #
    @57
    @58
    yonedalem21
    oveq12d
    eleqtrd
    @29
    cT
    cV
    @30
    @32
    cW
    @18
    @22
    yoneda.t
    @86
    @29
    cU
    cV
    @18
    wph
    cU
    cV
    wss
    @28
    @10
    adantr
    @29
    @77
    @18
    cU
    @84
    @29
    @77
    cS
    cbs
    cfv
    #
    cU
    @29
    cB
    @91
    @15
    @76
    @29
    cB
    @91
    cO
    cS
    @76
    @20
    c2nd
    cfv
    #
    @73
    @91
    eqid
    #
    @29
    @40
    wrel
    #
    @51
    @76
    @92
    @40
    wbr
    cO
    cS
    relfunc
    #
    @57
    @20
    @40
    1st2ndbr
    sylancr
    funcf1
    #
    @58
    ffvelrnd
    wph
    cU
    @91
    wceq
    #
    @28
    wph
    cS
    cU
    cvv
    yoneda.s
    @11
    setcbas
    adantr
    #
    eleqtrrd
    eqeltrrd
    sseldd
    @29
    @19
    @20
    @8
    co
    #
    @22
    cV
    @29
    @40
    cQ
    @8
    @21
    @19
    @20
    @8
    eqid
    #
    @53
    cO
    cS
    cQ
    @21
    yoneda.q
    @21
    eqid
    #
    fuchom
    #
    @29
    cB
    @40
    @15
    @0
    @55
    @58
    ffvelrnd
    #
    @57
    homfval
    @29
    @9
    cV
    @99
    wph
    @9
    cV
    wss
    @28
    wph
    @9
    cU
    cV
    yoneda.v
    unssad
    adantr
    @29
    @8
    @40
    @40
    cxp
    wfn
    #
    @19
    @40
    wcel
    #
    @51
    @99
    @9
    wcel
    @104
    @29
    @40
    cQ
    @8
    @100
    @53
    homffn
    a1i
    @103
    @57
    @40
    @40
    @19
    @20
    @8
    fnovrn
    syl3anc
    sseldd
    eqeltrrd
    @74
    setciso
    mpbid
    #
    @29
    @30
    @23
    wceq
    @31
    @24
    wb
    @29
    vh
    @18
    vh
    cv
    #
    @30
    cfv
    #
    cmpt
    vh
    @18
    @107
    @23
    cfv
    #
    cmpt
    @30
    @23
    @29
    vh
    @18
    @108
    @109
    @29
    @107
    @18
    wcel
    #
    wa
    #
    vy
    cB
    vg
    vy
    cv
    #
    @15
    @17
    co
    #
    @107
    vg
    cv
    #
    @15
    @112
    @92
    co
    cfv
    cfv
    #
    cmpt
    #
    cmpt
    vy
    cB
    @112
    @109
    cfv
    #
    cmpt
    #
    @108
    @109
    @111
    vy
    cB
    @116
    @117
    @111
    @112
    cB
    wcel
    #
    wa
    #
    @116
    vg
    @112
    @19
    c1st
    cfv
    #
    cfv
    #
    @114
    @117
    cfv
    #
    cmpt
    @117
    @120
    vg
    @113
    @115
    @122
    @123
    @120
    @122
    @113
    @120
    cB
    cC
    @17
    @15
    cY
    @112
    yoneda.y
    yoneda.b
    @111
    @79
    @119
    @29
    @79
    @110
    @82
    adantr
    #
    adantr
    #
    @111
    @26
    @119
    @29
    @26
    @110
    @58
    adantr
    #
    adantr
    #
    @83
    @111
    @119
    simpr
    #
    yon11
    eqcomd
    @120
    @114
    @113
    wcel
    #
    wa
    #
    @115
    @107
    @114
    @112
    @15
    cop
    @16
    cC
    cco
    cfv
    #
    co
    co
    @123
    @130
    cB
    cC
    @131
    @114
    @107
    @17
    @112
    @16
    cY
    @15
    yoneda.y
    yoneda.b
    @120
    @79
    @129
    @125
    adantr
    #
    @29
    @27
    @110
    @119
    @129
    @56
    ad3antrrr
    #
    @83
    @120
    @26
    @129
    @127
    adantr
    #
    @131
    eqid
    #
    @120
    @119
    @129
    @128
    adantr
    #
    @120
    @129
    simpr
    #
    @29
    @110
    @119
    @129
    simpllr
    #
    yon12
    @130
    cB
    cC
    @131
    @107
    @114
    @17
    @112
    @15
    cY
    @16
    yoneda.y
    yoneda.b
    @132
    @134
    @83
    @133
    @135
    @136
    @138
    @137
    yon2
    eqtr4d
    mpteq12dva
    @120
    vg
    @122
    @112
    @76
    cfv
    #
    @117
    @120
    @117
    @122
    @139
    cS
    chom
    cfv
    #
    co
    wcel
    @122
    @139
    @117
    wf
    @120
    @109
    cB
    cO
    cS
    @121
    @19
    c2nd
    cfv
    #
    @140
    @76
    @92
    @21
    @112
    @101
    @111
    @109
    @121
    @141
    cop
    @76
    @92
    cop
    @21
    co
    wcel
    @119
    @111
    @109
    cO
    cS
    @19
    @20
    @21
    @101
    @29
    @18
    @22
    @107
    @23
    @29
    cB
    cC
    cQ
    @0
    @1
    @17
    @21
    @15
    @16
    yoneda.b
    @83
    @102
    wph
    @14
    @28
    @25
    adantr
    @58
    @56
    funcf2
    #
    ffvelrnda
    nat1st2nd
    #
    adantr
    @73
    @140
    eqid
    #
    @128
    natcl
    @120
    cS
    cU
    @117
    @140
    cvv
    @122
    @139
    yoneda.s
    @29
    @81
    @110
    @119
    wph
    @81
    @28
    @11
    adantr
    ad2antrr
    @144
    @120
    @122
    @91
    cU
    @111
    cB
    @91
    @112
    @121
    @111
    cB
    @91
    cO
    cS
    @121
    @141
    @73
    @93
    @111
    @94
    @105
    @121
    @141
    @40
    wbr
    @95
    @111
    cB
    @40
    @15
    @0
    wph
    @52
    @28
    @110
    @54
    ad2antrr
    @126
    ffvelrnd
    @19
    @40
    1st2ndbr
    sylancr
    funcf1
    ffvelrnda
    @29
    @97
    @110
    @119
    @98
    ad2antrr
    #
    eleqtrrd
    @120
    @139
    @91
    cU
    @111
    cB
    @91
    @112
    @76
    @29
    cB
    @91
    @76
    wf
    @110
    @96
    adantr
    ffvelrnda
    @145
    eleqtrrd
    elsetchom
    mpbid
    feqmptd
    eqtr4d
    mpteq2dva
    @111
    vx
    vy
    vu
    @107
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
    @20
    cH
    cN
    cO
    cV
    cW
    @15
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
    @124
    @29
    @85
    @110
    @86
    adantr
    @29
    @87
    @110
    @88
    adantr
    @29
    @89
    @110
    @90
    adantr
    @29
    @51
    @110
    @57
    adantr
    @126
    yonedainv.n
    @29
    @107
    @77
    wcel
    @110
    @29
    @77
    @18
    @107
    @84
    eleq2d
    biimpar
    yonedalem4a
    @111
    @109
    cB
    wfn
    @109
    @118
    wceq
    @111
    @109
    cB
    cO
    cS
    @121
    @141
    @76
    @92
    @21
    @101
    @143
    @73
    natfn
    vy
    cB
    @109
    dffn5
    sylib
    3eqtr4d
    mpteq2dva
    @29
    vh
    @18
    @22
    @30
    @29
    @31
    @18
    @22
    @30
    wf
    @106
    @18
    @22
    @30
    f1of
    syl
    feqmptd
    @29
    vh
    @18
    @22
    @23
    @142
    feqmptd
    3eqtr4d
    @18
    @22
    @30
    @23
    f1oeq1
    syl
    mpbid
    ralrimivva
    vz
    vw
    cB
    cC
    cQ
    @0
    @1
    @17
    @21
    yoneda.b
    @83
    @102
    isffth2
    sylanbrc
    @0
    @1
    @3
    df-br
    sylib
    eqeltrd
end
