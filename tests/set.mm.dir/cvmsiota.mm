include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "crio.mm"
include "wreu.mm"
include "cvmseu.mm"
include "riotacl2.mm"
include "syl.mm"
include "syl5eqel.mm"
include "eleq2.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "sylib.mm"

theorem cvmsiota
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cW: class W
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cV: class V
  let cX: class X
  assume cvmcov.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmseu.1: |- B = U. C
  assume cvmsiota.2: |- W = ( iota_ x e. T A e. x )

  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint C k
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint C s
  disjoint u v
  disjoint u x
  disjoint C u
  disjoint v x
  disjoint C v
  disjoint C x
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint S x
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint U x
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint W v
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint B v
  disjoint B x
  disjoint a b
  disjoint a k
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b k
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint k t
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint s t
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint C t
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint J a
  disjoint J b
  disjoint J t
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint S t
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint U t
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint T z
  disjoint V a
  disjoint V b
  disjoint V k
  disjoint V s
  disjoint V t
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A t
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B w
  disjoint B y
  disjoint B z
  assert |- ( ( F e. ( C CovMap J ) /\ ( T e. ( S ` U ) /\ A e. B /\ ( F ` A ) e. U ) ) -> ( W e. T /\ A e. W ) )

  proof
    cF
    cC
    cJ
    ccvm
    co
    wcel
    cT
    cU
    cS
    cfv
    wcel
    cA
    cB
    wcel
    cA
    cF
    cfv
    cU
    wcel
    w3a
    wa
    #
    cW
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cT
    crab
    #
    wcel
    cW
    cT
    wcel
    cA
    cW
    wcel
    #
    wa
    @0
    cW
    @2
    vx
    cT
    crio
    #
    @3
    cvmsiota.2
    @0
    @2
    vx
    cT
    wreu
    @5
    @3
    wcel
    vx
    vv
    vu
    cA
    cB
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmseu.1
    cvmseu
    @2
    vx
    cT
    riotacl2
    syl
    syl5eqel
    cA
    vv
    cv
    #
    wcel
    #
    @4
    vv
    cW
    cT
    @3
    @6
    cW
    cA
    eleq2
    @2
    @7
    vx
    vv
    cT
    @1
    @6
    cA
    eleq2
    cbvrabv
    elrab2
    sylib
end
