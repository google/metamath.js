include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "cnat.mm"
include "cv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wf.mm"
include "cfunc.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "oveq12d.mm"
include "fveq12d.mm"
include "mpteq12dv.mm"
include "ovex.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"
include "chom.mm"
include "c2nd.mm"
include "eqid.mm"
include "nat1st2nd.mm"
include "oppcbas.mm"
include "adantr.mm"
include "natcl.mm"
include "cvv.mm"
include "chomf.mm"
include "crn.mm"
include "unssbd.mm"
include "ssexd.mm"
include "cbs.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "yon1cl.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "setcbas.mm"
include "eleqtrrd.mm"
include "elsetchom.mm"
include "mpbid.mm"
include "catidcl.mm"
include "yon11.mm"
include "fmptd.mm"
include "yonedalem21.mm"
include "ccat.mm"
include "oppccat.mm"
include "syl.mm"
include "setccat.mm"
include "evlf1.mm"
include "feq123d.mm"
include "mpbird.mm"
include "jca.mm"

theorem yonedalem3a
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
  let cF: class F
  let cH: class H
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
  let cA: class A
  let vv: setvar v
  let cK: class K
  let cG: class G
  let cN: class N
  let cI: class I
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
  assume yonedalem3a.m: |- M = ( f e. ( O Func S ) , x e. B |-> ( a e. ( ( ( 1st ` Y ) ` x ) ( O Nat S ) f ) |-> ( ( a ` x ) ` ( .1. ` x ) ) ) )

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
  disjoint F a
  disjoint F f
  disjoint F x
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
  disjoint F b
  disjoint F g
  disjoint F h
  disjoint k x
  disjoint F k
  disjoint F u
  disjoint F w
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
  disjoint X b
  disjoint X g
  disjoint X h
  disjoint X k
  disjoint X u
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( ( F M X ) = ( a e. ( ( ( 1st ` Y ) ` X ) ( O Nat S ) F ) |-> ( ( a ` X ) ` ( .1. ` X ) ) ) /\ ( F M X ) : ( F ( 1st ` Z ) X ) --> ( F ( 1st ` E ) X ) ) )

  proof
    wph
    cF
    cX
    cM
    co
    #
    va
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
    cmpt
    #
    wceq
    #
    cF
    cX
    cZ
    c1st
    cfv
    co
    #
    cF
    cX
    cE
    c1st
    cfv
    co
    #
    @0
    wf
    #
    wph
    cF
    cO
    cS
    cfunc
    co
    #
    wcel
    #
    cX
    cB
    wcel
    #
    @10
    yonedalem21.f
    yonedalem21.x
    vf
    vx
    cF
    cX
    @14
    cB
    va
    vx
    cv
    #
    @1
    cfv
    #
    vf
    cv
    #
    @3
    co
    #
    @17
    c.1
    cfv
    #
    @17
    @6
    cfv
    #
    cfv
    #
    cmpt
    @9
    cM
    @19
    cF
    wceq
    #
    @17
    cX
    wceq
    #
    wa
    #
    va
    @20
    @23
    @4
    @8
    @26
    @18
    @2
    @19
    cF
    @3
    @26
    @17
    cX
    @1
    @24
    @25
    simpr
    #
    fveq2d
    @24
    @25
    simpl
    oveq12d
    @26
    @21
    @5
    @22
    @7
    @26
    @17
    cX
    @6
    @27
    fveq2d
    @26
    @17
    cX
    c.1
    @27
    fveq2d
    fveq12d
    mpteq12dv
    yonedalem3a.m
    va
    @4
    @8
    @2
    cF
    @3
    ovex
    mptex
    ovmpt2a
    syl2anc
    #
    wph
    @13
    @4
    cX
    cF
    c1st
    cfv
    #
    cfv
    #
    @9
    wf
    wph
    va
    @4
    @8
    @30
    @9
    wph
    @6
    @4
    wcel
    #
    wa
    #
    cX
    @2
    c1st
    cfv
    #
    cfv
    #
    @30
    @5
    @7
    @32
    @7
    @34
    @30
    cS
    chom
    cfv
    #
    co
    wcel
    @34
    @30
    @7
    wf
    @32
    @6
    cB
    cO
    cS
    @33
    @2
    c2nd
    cfv
    #
    @35
    @29
    cF
    c2nd
    cfv
    #
    @3
    cX
    @3
    eqid
    #
    @32
    @6
    cO
    cS
    @2
    cF
    @3
    @38
    wph
    @31
    simpr
    nat1st2nd
    cB
    cC
    cO
    yoneda.o
    yoneda.b
    oppcbas
    #
    @35
    eqid
    #
    wph
    @16
    @31
    yonedalem21.x
    adantr
    natcl
    @32
    cS
    cU
    @7
    @35
    cvv
    @34
    @30
    yoneda.s
    wph
    cU
    cvv
    wcel
    #
    @31
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
    adantr
    @40
    wph
    @34
    cU
    wcel
    @31
    wph
    @34
    cS
    cbs
    cfv
    #
    cU
    wph
    cB
    @43
    cX
    @33
    wph
    cB
    @43
    cO
    cS
    @33
    @36
    @39
    @43
    eqid
    #
    wph
    @14
    wrel
    #
    @2
    @14
    wcel
    @33
    @36
    @14
    wbr
    cO
    cS
    relfunc
    #
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
    @42
    yoneda.u
    yon1cl
    @2
    @14
    1st2ndbr
    sylancr
    funcf1
    yonedalem21.x
    ffvelrnd
    wph
    cS
    cU
    cvv
    yoneda.s
    @42
    setcbas
    #
    eleqtrrd
    adantr
    wph
    @30
    cU
    wcel
    @31
    wph
    @30
    @43
    cU
    wph
    cB
    @43
    cX
    @29
    wph
    cB
    @43
    cO
    cS
    @29
    @37
    @39
    @44
    wph
    @45
    @15
    @29
    @37
    @14
    wbr
    @46
    yonedalem21.f
    cF
    @14
    1st2ndbr
    sylancr
    funcf1
    yonedalem21.x
    ffvelrnd
    @47
    eleqtrrd
    adantr
    elsetchom
    mpbid
    wph
    @5
    @34
    wcel
    @31
    wph
    @5
    cX
    cX
    cC
    chom
    cfv
    #
    co
    @34
    wph
    cB
    cC
    c.1
    @48
    cX
    yoneda.b
    @48
    eqid
    #
    yoneda.1
    yoneda.c
    yonedalem21.x
    catidcl
    wph
    cB
    cC
    @48
    cX
    cY
    cX
    yoneda.y
    yoneda.b
    yoneda.c
    yonedalem21.x
    @49
    yonedalem21.x
    yon11
    eleqtrrd
    adantr
    ffvelrnd
    @9
    eqid
    fmptd
    wph
    @11
    @4
    @12
    @30
    @0
    @9
    @28
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
    wph
    cB
    cO
    cS
    cE
    cF
    cX
    yoneda.e
    wph
    cC
    ccat
    wcel
    cO
    ccat
    wcel
    yoneda.c
    cC
    cO
    yoneda.o
    oppccat
    syl
    wph
    @41
    cS
    ccat
    wcel
    @42
    cS
    cU
    cvv
    yoneda.s
    setccat
    syl
    @39
    yonedalem21.f
    yonedalem21.x
    evlf1
    feq123d
    mpbird
    jca
end
