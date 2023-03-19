include "cofr.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "wceq.mm"
include "id.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "mpbird.mm"

theorem caofref
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cV: class V
  let vw: setvar w
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cH: class H
  let cO: class O
  let cP: class P
  let cT: class T
  let cU: class U
  assume caofref.1: |- ( ph -> A e. V )
  assume caofref.2: |- ( ph -> F : A --> S )
  assume caofref.3: |- ( ( ph /\ x e. S ) -> x R x )

  disjoint F x
  disjoint ph x
  disjoint R x
  disjoint S x
  disjoint w x
  disjoint B w
  disjoint B x
  disjoint C w
  disjoint C x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G w
  disjoint G x
  disjoint G y
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
  disjoint ph y
  disjoint ph z
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint A w
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  assert |- ( ph -> F oR R F )

  proof
    wph
    cF
    cF
    cR
    cofr
    wbr
    vw
    cv
    #
    cF
    cfv
    #
    @1
    cR
    wbr
    #
    vw
    cA
    wral
    wph
    @2
    vw
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    cS
    wcel
    vx
    cv
    #
    @5
    cR
    wbr
    #
    vx
    cS
    wral
    #
    @2
    wph
    cA
    cS
    @0
    cF
    caofref.2
    ffvelrnda
    wph
    @7
    @3
    wph
    @6
    vx
    cS
    caofref.3
    ralrimiva
    adantr
    @6
    @2
    vx
    @1
    cS
    @5
    @1
    wceq
    #
    @5
    @1
    @5
    @1
    cR
    @8
    id
    #
    @9
    breq12d
    rspcv
    sylc
    ralrimiva
    wph
    vw
    cA
    cA
    @1
    @1
    cR
    cA
    cF
    cF
    cV
    cV
    wph
    cA
    cS
    cF
    wf
    cF
    cA
    wfn
    caofref.2
    cA
    cS
    cF
    ffn
    syl
    #
    @10
    caofref.1
    caofref.1
    cA
    inidm
    @4
    @1
    eqidd
    #
    @11
    ofrfval
    mpbird
end
