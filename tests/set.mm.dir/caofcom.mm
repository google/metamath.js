include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cof.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "ffvelrnda.mm"
include "jca.mm"
include "caovcomg.mm"
include "syldan.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem caofcom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cV: class V
  let vw: setvar w
  let cB: class B
  let cC: class C
  let vz: setvar z
  let cH: class H
  let cO: class O
  let cP: class P
  let cT: class T
  let cU: class U
  assume caofref.1: |- ( ph -> A e. V )
  assume caofref.2: |- ( ph -> F : A --> S )
  assume caofcom.3: |- ( ph -> G : A --> S )
  assume caofcom.4: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x R y ) = ( y R x ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint w x
  disjoint B w
  disjoint B x
  disjoint C w
  disjoint C x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G w
  disjoint G z
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint ph w
  disjoint ph z
  disjoint R w
  disjoint R z
  disjoint A w
  disjoint S w
  disjoint S z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  assert |- ( ph -> ( F oF R G ) = ( G oF R F ) )

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
    cR
    co
    #
    cmpt
    vw
    cA
    @2
    @1
    cR
    co
    #
    cmpt
    cF
    cG
    cR
    cof
    #
    co
    cG
    cF
    @5
    co
    wph
    vw
    cA
    @3
    @4
    wph
    @0
    cA
    wcel
    #
    @1
    cS
    wcel
    #
    @2
    cS
    wcel
    #
    wa
    @3
    @4
    wceq
    wph
    @6
    wa
    @7
    @8
    wph
    cA
    cS
    @0
    cF
    caofref.2
    ffvelrnda
    #
    wph
    cA
    cS
    @0
    cG
    caofcom.3
    ffvelrnda
    #
    jca
    wph
    vx
    vy
    @1
    @2
    cS
    cR
    caofcom.4
    caovcomg
    syldan
    mpteq2dva
    wph
    vw
    cA
    @1
    @2
    cR
    cF
    cG
    cV
    cS
    cS
    caofref.1
    @9
    @10
    wph
    vw
    cA
    cS
    cF
    caofref.2
    feqmptd
    #
    wph
    vw
    cA
    cS
    cG
    caofcom.3
    feqmptd
    #
    offval2
    wph
    vw
    cA
    @2
    @1
    cR
    cG
    cF
    cV
    cS
    cS
    caofref.1
    @10
    @9
    @12
    @11
    offval2
    3eqtr4d
end
