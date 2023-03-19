include "cv.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "c2nd.mm"
include "cmpt.mm"
include "c1st.mm"
include "cvv.mm"
include "cfunc.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "fveq2d.mm"
include "simprr.mm"
include "fveq12d.mm"
include "wcel.mm"
include "simplrr.mm"
include "oveq2d.mm"
include "simplrl.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "fveq1d.mm"
include "mpteq12dv.mm"
include "mpteq2dva.mm"
include "fvex.mm"
include "mptex.mm"
include "ovmpt2d.mm"
include "simpr.mm"
include "mpteq2dv.mm"
include "cbs.mm"
include "eqeltri.mm"
include "fvmptd.mm"

theorem yonedalem4a
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
  assert |- ( ph -> ( ( F N X ) ` A ) = ( y e. B |-> ( g e. ( y ( Hom ` C ) X ) |-> ( ( ( X ( 2nd ` F ) y ) ` g ) ` A ) ) ) )

  proof
    wph
    vu
    cA
    vy
    cB
    vg
    vy
    cv
    #
    cX
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
    cX
    @0
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
    cmpt
    #
    cmpt
    #
    vy
    cB
    vg
    @2
    cA
    @7
    cfv
    #
    cmpt
    #
    cmpt
    #
    cX
    cF
    c1st
    cfv
    #
    cfv
    #
    cF
    cX
    cN
    co
    cvv
    wph
    vf
    vx
    cF
    cX
    cO
    cS
    cfunc
    co
    #
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
    @0
    @17
    @1
    co
    #
    @3
    @4
    @17
    @0
    @18
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
    vu
    @15
    @10
    cmpt
    #
    cN
    cvv
    cN
    vf
    vx
    @16
    cB
    @28
    cmpt2
    wceq
    wph
    yonedalem4.n
    a1i
    wph
    @18
    cF
    wceq
    #
    @17
    cX
    wceq
    #
    wa
    wa
    #
    vu
    @20
    @27
    @15
    @10
    @32
    @17
    cX
    @19
    @14
    @32
    @18
    cF
    c1st
    wph
    @30
    @31
    simprl
    fveq2d
    wph
    @30
    @31
    simprr
    fveq12d
    @32
    vy
    cB
    @26
    @9
    @32
    @0
    cB
    wcel
    #
    wa
    #
    vg
    @21
    @25
    @2
    @8
    @34
    @17
    cX
    @0
    @1
    wph
    @30
    @31
    @33
    simplrr
    #
    oveq2d
    @34
    @3
    @24
    @7
    @34
    @4
    @23
    @6
    @34
    @17
    cX
    @0
    @0
    @22
    @5
    @34
    @18
    cF
    c2nd
    wph
    @30
    @31
    @33
    simplrl
    fveq2d
    @35
    @34
    @0
    eqidd
    oveq123d
    fveq1d
    fveq1d
    mpteq12dv
    mpteq2dva
    mpteq12dv
    yonedalem21.f
    yonedalem21.x
    @29
    cvv
    wcel
    wph
    vu
    @15
    @10
    cX
    @14
    fvex
    mptex
    a1i
    ovmpt2d
    wph
    @3
    cA
    wceq
    #
    wa
    #
    vy
    cB
    @9
    @12
    @37
    vg
    @2
    @8
    @11
    @37
    @3
    cA
    @7
    wph
    @36
    simpr
    fveq2d
    mpteq2dv
    mpteq2dv
    yonedalem4.p
    @13
    cvv
    wcel
    wph
    vy
    cB
    @12
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
    a1i
    fvmptd
end
