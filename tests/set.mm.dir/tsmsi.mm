include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "ctsu.mm"
include "wa.mm"
include "eltsms.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "eleq2.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"

theorem tsmsi
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let vu: setvar u
  let vw: setvar w
  assume eltsms.b: |- B = ( Base ` G )
  assume eltsms.j: |- J = ( TopOpen ` G )
  assume eltsms.s: |- S = ( ~P A i^i Fin )
  assume eltsms.1: |- ( ph -> G e. CMnd )
  assume eltsms.2: |- ( ph -> G e. TopSp )
  assume eltsms.a: |- ( ph -> A e. V )
  assume eltsms.f: |- ( ph -> F : A --> B )
  assume tsmsi.3: |- ( ph -> C e. ( G tsums F ) )
  assume tsmsi.4: |- ( ph -> U e. J )
  assume tsmsi.5: |- ( ph -> C e. U )

  disjoint B y
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint J z
  disjoint A z
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint S z
  disjoint U y
  disjoint U z
  disjoint u w
  disjoint u y
  disjoint B u
  disjoint w y
  disjoint B w
  disjoint C u
  disjoint C w
  disjoint u z
  disjoint F u
  disjoint w z
  disjoint F w
  disjoint G u
  disjoint G w
  disjoint J u
  disjoint J w
  disjoint ph u
  disjoint S u
  disjoint S w
  disjoint U u
  assert |- ( ph -> E. z e. S A. y e. S ( z C_ y -> ( G gsum ( F |` y ) ) e. U ) )

  proof
    wph
    cU
    cJ
    wcel
    cC
    vu
    cv
    #
    wcel
    #
    vz
    cv
    vy
    cv
    #
    wss
    #
    cG
    cF
    @2
    cres
    cgsu
    co
    #
    @0
    wcel
    #
    wi
    #
    vy
    cS
    wral
    vz
    cS
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    cC
    cU
    wcel
    #
    @3
    @4
    cU
    wcel
    #
    wi
    #
    vy
    cS
    wral
    vz
    cS
    wrex
    #
    tsmsi.4
    wph
    cC
    cB
    wcel
    #
    @9
    wph
    cC
    cG
    cF
    ctsu
    co
    wcel
    @14
    @9
    wa
    tsmsi.3
    wph
    vy
    vz
    vu
    cA
    cB
    cC
    cS
    cF
    cG
    cJ
    cV
    eltsms.b
    eltsms.j
    eltsms.s
    eltsms.1
    eltsms.2
    eltsms.a
    eltsms.f
    eltsms
    mpbid
    simprd
    tsmsi.5
    @8
    @10
    @13
    wi
    vu
    cU
    cJ
    @0
    cU
    wceq
    #
    @1
    @10
    @7
    @13
    @0
    cU
    cC
    eleq2
    @15
    @6
    @12
    vz
    vy
    cS
    cS
    @15
    @5
    @11
    @3
    @0
    cU
    @4
    eleq2
    imbi2d
    rexralbidv
    imbi12d
    rspcv
    syl3c
end
