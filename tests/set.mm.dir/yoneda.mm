include "cxpc.mm"
include "co.mm"
include "cfunc.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "chom.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cinv.mm"
include "fucbas.mm"
include "eqid.mm"
include "ccat.mm"
include "wcel.mm"
include "wa.mm"
include "yonedalem1.mm"
include "simpld.mm"
include "funcrcl.mm"
include "syl.mm"
include "simprd.mm"
include "fuccat.mm"
include "yonedainv.mm"
include "inviso1.mm"

theorem yoneda
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
  let cI: class I
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
  assume yoneda.i: |- I = ( Iso ` R )

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
  assert |- ( ph -> M e. ( Z I E ) )

  proof
    wph
    cQ
    cO
    cxpc
    co
    #
    cT
    cfunc
    co
    #
    cR
    cM
    vf
    vx
    cO
    cS
    cfunc
    co
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
    cfv
    vy
    cB
    vg
    vy
    cv
    #
    @2
    cC
    chom
    cfv
    co
    vu
    cv
    vg
    cv
    @2
    @4
    @3
    c2nd
    cfv
    co
    cfv
    cfv
    cmpt
    cmpt
    cmpt
    cmpt2
    #
    cI
    cR
    cinv
    cfv
    #
    cZ
    cE
    @0
    cT
    cR
    yoneda.r
    fucbas
    @6
    eqid
    #
    wph
    @0
    cT
    cR
    yoneda.r
    wph
    @0
    ccat
    wcel
    #
    cT
    ccat
    wcel
    #
    wph
    cZ
    @1
    wcel
    #
    @8
    @9
    wa
    wph
    @10
    cE
    @1
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
    @0
    cT
    cZ
    funcrcl
    syl
    #
    simpld
    wph
    @8
    @9
    @14
    simprd
    fuccat
    @13
    wph
    @10
    @11
    @12
    simprd
    yoneda.i
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
    @6
    cM
    @5
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
    @7
    @5
    eqid
    yonedainv
    inviso1
end
