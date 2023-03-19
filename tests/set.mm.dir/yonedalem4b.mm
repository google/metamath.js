include "co.mm"
include "cfv.mm"
include "cv.mm"
include "chom.mm"
include "c2nd.mm"
include "cmpt.mm"
include "yonedalem4a.mm"
include "fveq1d.mm"
include "wceq.mm"
include "eqidd.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "ovex.mm"
include "mptex.mm"
include "a1i.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "fvexd.mm"
include "simplr.mm"
include "oveq2d.mm"
include "fveq12d.mm"
include "fvmptdv2.mm"
include "nfmpt1.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq1.mm"
include "fvmptdf.mm"
include "mpd.mm"
include "eqtrd.mm"

theorem yonedalem4b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
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
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
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
  let cI: class I
  let cM: class M
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
  assume yonedalem4b.p: |- ( ph -> P e. B )
  assume yonedalem4b.g: |- ( ph -> G e. ( P ( Hom ` C ) X ) )

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
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint G y
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
  disjoint P f
  disjoint P g
  disjoint P x
  disjoint P y
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
  assert |- ( ph -> ( ( ( ( F N X ) ` A ) ` P ) ` G ) = ( ( ( X ( 2nd ` F ) P ) ` G ) ` A ) )

  proof
    wph
    cG
    cP
    cA
    cF
    cX
    cN
    co
    cfv
    #
    cfv
    #
    cfv
    cG
    cP
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
    cA
    vg
    cv
    #
    cX
    @2
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
    cfv
    #
    cfv
    #
    cA
    cG
    cX
    cP
    @6
    co
    #
    cfv
    #
    cfv
    #
    wph
    cG
    @1
    @12
    wph
    cP
    @0
    @11
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
    fveq1d
    fveq1d
    wph
    @11
    @11
    wceq
    @13
    @16
    wceq
    #
    wph
    @11
    eqidd
    wph
    @17
    vy
    cP
    @10
    cB
    @11
    cvv
    yonedalem4b.p
    @10
    cvv
    wcel
    wph
    @2
    cP
    wceq
    #
    wa
    #
    vg
    @4
    @9
    @2
    cX
    @3
    ovex
    mptex
    a1i
    @19
    vg
    cG
    @9
    @16
    @4
    @12
    cvv
    @19
    cG
    cP
    cX
    @3
    co
    #
    @4
    wph
    cG
    @20
    wcel
    @18
    yonedalem4b.g
    adantr
    @19
    @2
    cP
    cX
    @3
    wph
    @18
    simpr
    oveq1d
    eleqtrrd
    @19
    @5
    cG
    wceq
    #
    wa
    #
    cA
    @8
    fvexd
    @22
    cA
    @8
    @15
    @22
    @5
    cG
    @7
    @14
    @22
    @2
    cP
    cX
    @6
    wph
    @18
    @21
    simplr
    oveq2d
    @19
    @21
    simpr
    fveq12d
    fveq1d
    fvmptdv2
    vy
    cB
    @10
    nfmpt1
    vy
    @13
    @16
    vy
    cG
    @12
    vy
    cB
    @10
    cP
    nffvmpt1
    vy
    cG
    nfcv
    nffv
    nfeq1
    fvmptdf
    mpd
    eqtrd
end
