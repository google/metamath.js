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
include "caovdid.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem caofdi
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
  assume caofdi.5: |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) -> ( x T ( y R z ) ) = ( ( x T y ) O ( x T z ) ) )

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
  assert |- ( ph -> ( F oF T ( G oF R H ) ) = ( ( F oF T G ) oF O ( F oF T H ) ) )

  proof
    wph
    vw
    cA
    vw
    cv
    #
    cF
    cfv
    #
    @0
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
    cT
    co
    #
    cmpt
    vw
    cA
    @1
    @2
    cT
    co
    #
    @1
    @3
    cT
    co
    #
    cO
    co
    #
    cmpt
    cF
    cG
    cH
    cR
    cof
    co
    #
    cT
    cof
    #
    co
    cF
    cG
    @10
    co
    #
    cF
    cH
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
    @3
    cS
    cR
    cT
    cO
    cK
    wph
    vx
    cv
    #
    cK
    wcel
    vy
    cv
    #
    cS
    wcel
    vz
    cv
    #
    cS
    wcel
    w3a
    @15
    @16
    @17
    cR
    co
    cT
    co
    @15
    @16
    cT
    co
    @15
    @17
    cT
    co
    cO
    co
    wceq
    @13
    caofdi.5
    adantlr
    wph
    cA
    cK
    @0
    cF
    caofdi.2
    ffvelrnda
    #
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
    caovdid
    mpteq2dva
    wph
    vw
    cA
    @1
    @4
    cT
    cF
    @9
    cV
    cK
    cvv
    caofdi.1
    @18
    @14
    @2
    @3
    cR
    ovexd
    wph
    vw
    cA
    cK
    cF
    caofdi.2
    feqmptd
    #
    wph
    vw
    cA
    @2
    @3
    cR
    cG
    cH
    cV
    cS
    cS
    caofdi.1
    @19
    @20
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
    @2
    cT
    ovexd
    @14
    @1
    @3
    cT
    ovexd
    wph
    vw
    cA
    @1
    @2
    cT
    cF
    cG
    cV
    cK
    cS
    caofdi.1
    @18
    @19
    @21
    @22
    offval2
    wph
    vw
    cA
    @1
    @3
    cT
    cF
    cH
    cV
    cK
    cS
    caofdi.1
    @18
    @20
    @21
    @23
    offval2
    offval2
    3eqtr4d
end
