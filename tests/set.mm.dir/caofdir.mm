include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cof.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wceq.mm"
include "adantlr.mm"
include "ffvelrnda.mm"
include "caovdird.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem caofdir
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let vw: setvar w
  assume caofdi.1: |- ( ph -> A e. V )
  assume caofdi.2: |- ( ph -> F : A --> K )
  assume caofdi.3: |- ( ph -> G : A --> S )
  assume caofdi.4: |- ( ph -> H : A --> S )
  assume caofdir.5: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) -> ( ( x R y ) T z ) = ( ( x T z ) O ( y T z ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint F w
  disjoint G w
  disjoint ph w
  disjoint H w
  disjoint K w
  disjoint O w
  disjoint R w
  disjoint S w
  disjoint T w
  assert |- ( ph -> ( ( G oF R H ) oF T F ) = ( ( G oF T F ) oF O ( H oF T F ) ) )

  proof
    wph
    vw
    cA
    vw
    cv
    #
    cG
    cfv
    #
    @0
    cH
    cfv
    #
    cR
    co
    #
    @0
    cF
    cfv
    #
    cT
    co
    #
    cmpt
    vw
    cA
    @1
    @4
    cT
    co
    #
    @2
    @4
    cT
    co
    #
    cO
    co
    #
    cmpt
    cG
    cH
    cR
    cof
    co
    #
    cF
    cT
    cof
    #
    co
    cG
    cF
    @10
    co
    #
    cH
    cF
    @10
    co
    #
    cO
    cof
    co
    wph
    vw
    cA
    @5
    @8
    wph
    @0
    cA
    wcel
    #
    wa
    #
    vx
    vy
    vz
    @1
    @2
    @4
    cS
    cR
    cT
    cO
    cK
    wph
    vx
    cv
    #
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    vz
    cv
    #
    cK
    wcel
    w3a
    @15
    @16
    cR
    co
    @17
    cT
    co
    @15
    @17
    cT
    co
    @16
    @17
    cT
    co
    cO
    co
    wceq
    @13
    caofdir.5
    adantlr
    wph
    cA
    cS
    @0
    cG
    caofdi.3
    ffvelrnda
    #
    wph
    cA
    cS
    @0
    cH
    caofdi.4
    ffvelrnda
    #
    wph
    cA
    cK
    @0
    cF
    caofdi.2
    ffvelrnda
    #
    caovdird
    mpteq2dva
    wph
    vw
    cA
    @3
    @4
    cT
    @9
    cF
    cV
    cvv
    cK
    caofdi.1
    @14
    @1
    @2
    cR
    ovexd
    @20
    wph
    vw
    cA
    @1
    @2
    cR
    cG
    cH
    cV
    cS
    cS
    caofdi.1
    @18
    @19
    wph
    vw
    cA
    cS
    cG
    caofdi.3
    feqmptd
    #
    wph
    vw
    cA
    cS
    cH
    caofdi.4
    feqmptd
    #
    offval2
    wph
    vw
    cA
    cK
    cF
    caofdi.2
    feqmptd
    #
    offval2
    wph
    vw
    cA
    @6
    @7
    cO
    @11
    @12
    cV
    cvv
    cvv
    caofdi.1
    @14
    @1
    @4
    cT
    ovexd
    @14
    @2
    @4
    cT
    ovexd
    wph
    vw
    cA
    @1
    @4
    cT
    cG
    cF
    cV
    cS
    cK
    caofdi.1
    @18
    @20
    @21
    @23
    offval2
    wph
    vw
    cA
    @2
    @4
    cT
    cH
    cF
    cV
    cS
    cK
    caofdi.1
    @19
    @20
    @22
    @23
    offval2
    offval2
    3eqtr4d
end
