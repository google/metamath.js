include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cofc.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "ofcfval.mm"
include "wral.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "ralrimivva.mm"
include "ovrspc2v.mm"
include "syl21anc.mm"
include "fmpt3d.mm"

theorem ofcf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cV: class V
  let vz: setvar z
  assume ofcf.1: |- ( ( ph /\ ( x e. S /\ y e. T ) ) -> ( x R y ) e. U )
  assume ofcf.2: |- ( ph -> F : A --> S )
  assume ofcf.4: |- ( ph -> A e. V )
  assume ofcf.5: |- ( ph -> C e. T )

  disjoint C y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint U y
  disjoint ph x
  disjoint ph y
  disjoint A z
  disjoint y z
  disjoint C z
  disjoint x z
  disjoint F z
  disjoint R z
  disjoint U z
  disjoint ph z
  assert |- ( ph -> ( F oFC R C ) : A --> U )

  proof
    wph
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    #
    cC
    cR
    co
    #
    cU
    cF
    cC
    cR
    cofc
    co
    wph
    vz
    cA
    @1
    cC
    cR
    cF
    cV
    cT
    wph
    cA
    cS
    cF
    wf
    cF
    cA
    wfn
    ofcf.2
    cA
    cS
    cF
    ffn
    syl
    ofcf.4
    ofcf.5
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    eqidd
    ofcfval
    @4
    @1
    cS
    wcel
    cC
    cT
    wcel
    #
    vx
    cv
    vy
    cv
    cR
    co
    cU
    wcel
    #
    vy
    cT
    wral
    vx
    cS
    wral
    #
    @2
    cU
    wcel
    wph
    cA
    cS
    @0
    cF
    ofcf.2
    ffvelrnda
    wph
    @5
    @3
    ofcf.5
    adantr
    wph
    @7
    @3
    wph
    @6
    vx
    vy
    cS
    cT
    ofcf.1
    ralrimivva
    adantr
    vx
    vy
    cS
    cT
    cU
    cR
    @1
    cC
    ovrspc2v
    syl21anc
    fmpt3d
end
