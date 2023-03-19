include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cof.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wral.mm"
include "ralrimivvva.mm"
include "adantr.mm"
include "wi.mm"
include "ffvelrnda.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc3v.mm"
include "syl3anc.mm"
include "mpd.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem caofass
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cO: class O
  let cV: class V
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cU: class U
  assume caofref.1: |- ( ph -> A e. V )
  assume caofref.2: |- ( ph -> F : A --> S )
  assume caofcom.3: |- ( ph -> G : A --> S )
  assume caofass.4: |- ( ph -> H : A --> S )
  assume caofass.5: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x R y ) T z ) = ( x O ( y P z ) ) )

  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint ph x
  disjoint ph y
  disjoint ph z
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
  disjoint B w
  disjoint B x
  disjoint C w
  disjoint C x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint G w
  disjoint H w
  disjoint O w
  disjoint P w
  disjoint ph w
  disjoint R w
  disjoint A w
  disjoint S w
  disjoint T w
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  assert |- ( ph -> ( ( F oF R G ) oF T H ) = ( F oF O ( G oF P H ) ) )

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
    @0
    cH
    cfv
    #
    cT
    co
    #
    cmpt
    vw
    cA
    @1
    @2
    @4
    cP
    co
    #
    cO
    co
    #
    cmpt
    cF
    cG
    cR
    cof
    co
    #
    cH
    cT
    cof
    co
    cF
    cG
    cH
    cP
    cof
    co
    #
    cO
    cof
    co
    wph
    vw
    cA
    @5
    @7
    wph
    @0
    cA
    wcel
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    co
    #
    vz
    cv
    #
    cT
    co
    #
    @12
    @13
    @15
    cP
    co
    #
    cO
    co
    #
    wceq
    #
    vz
    cS
    wral
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @5
    @7
    wceq
    #
    wph
    @20
    @10
    wph
    @19
    vx
    vy
    vz
    cS
    cS
    cS
    caofass.5
    ralrimivvva
    adantr
    @11
    @1
    cS
    wcel
    @2
    cS
    wcel
    @4
    cS
    wcel
    @20
    @21
    wi
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
    wph
    cA
    cS
    @0
    cH
    caofass.4
    ffvelrnda
    #
    @19
    @21
    @1
    @13
    cR
    co
    #
    @15
    cT
    co
    #
    @1
    @17
    cO
    co
    #
    wceq
    @3
    @15
    cT
    co
    #
    @1
    @2
    @15
    cP
    co
    #
    cO
    co
    #
    wceq
    vx
    vy
    vz
    @1
    @2
    @4
    cS
    cS
    cS
    @12
    @1
    wceq
    #
    @16
    @26
    @18
    @27
    @31
    @14
    @25
    @15
    cT
    @12
    @1
    @13
    cR
    oveq1
    oveq1d
    @12
    @1
    @17
    cO
    oveq1
    eqeq12d
    @13
    @2
    wceq
    #
    @26
    @28
    @27
    @30
    @32
    @25
    @3
    @15
    cT
    @13
    @2
    @1
    cR
    oveq2
    oveq1d
    @32
    @17
    @29
    @1
    cO
    @13
    @2
    @15
    cP
    oveq1
    oveq2d
    eqeq12d
    @15
    @4
    wceq
    #
    @28
    @5
    @30
    @7
    @15
    @4
    @3
    cT
    oveq2
    @33
    @29
    @6
    @1
    cO
    @15
    @4
    @2
    cP
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    syl3anc
    mpd
    mpteq2dva
    wph
    vw
    cA
    @3
    @4
    cT
    @8
    cH
    cV
    cvv
    cS
    caofref.1
    @11
    @1
    @2
    cR
    ovexd
    @24
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
    @22
    @23
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
    cS
    cH
    caofass.4
    feqmptd
    #
    offval2
    wph
    vw
    cA
    @1
    @6
    cO
    cF
    @9
    cV
    cS
    cvv
    caofref.1
    @22
    @11
    @2
    @4
    cP
    ovexd
    @34
    wph
    vw
    cA
    @2
    @4
    cP
    cG
    cH
    cV
    cS
    cS
    caofref.1
    @23
    @24
    @35
    @36
    offval2
    offval2
    3eqtr4d
end
