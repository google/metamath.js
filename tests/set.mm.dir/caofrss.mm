include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wral.mm"
include "cofr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "ffvelrnda.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi12d.mm"
include "breq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "ralimdva.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "3imtr4d.mm"

theorem caofrss
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
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
  let cU: class U
  assume caofref.1: |- ( ph -> A e. V )
  assume caofref.2: |- ( ph -> F : A --> S )
  assume caofcom.3: |- ( ph -> G : A --> S )
  assume caofrss.4: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x R y -> x T y ) )

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
  disjoint T x
  disjoint T y
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
  disjoint T z
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  assert |- ( ph -> ( F oR R G -> F oR T G ) )

  proof
    wph
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
    wbr
    #
    vw
    cA
    wral
    @1
    @2
    cT
    wbr
    #
    vw
    cA
    wral
    cF
    cG
    cR
    cofr
    wbr
    cF
    cG
    cT
    cofr
    wbr
    wph
    @3
    @4
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
    @2
    cS
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @7
    @8
    cT
    wbr
    #
    wi
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @3
    @4
    wi
    #
    wph
    cA
    cS
    @0
    cF
    caofref.2
    ffvelrnda
    wph
    cA
    cS
    @0
    cG
    caofcom.3
    ffvelrnda
    wph
    @12
    @5
    wph
    @11
    vx
    vy
    cS
    cS
    caofrss.4
    ralrimivva
    adantr
    @11
    @13
    @1
    @8
    cR
    wbr
    #
    @1
    @8
    cT
    wbr
    #
    wi
    vx
    vy
    @1
    @2
    cS
    cS
    @7
    @1
    wceq
    @9
    @14
    @10
    @15
    @7
    @1
    @8
    cR
    breq1
    @7
    @1
    @8
    cT
    breq1
    imbi12d
    @8
    @2
    wceq
    @14
    @3
    @15
    @4
    @8
    @2
    @1
    cR
    breq2
    @8
    @2
    @1
    cT
    breq2
    imbi12d
    rspc2va
    syl21anc
    ralimdva
    wph
    vw
    cA
    cA
    @1
    @2
    cR
    cA
    cF
    cG
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
    wph
    cA
    cS
    cG
    wf
    cG
    cA
    wfn
    caofcom.3
    cA
    cS
    cG
    ffn
    syl
    #
    caofref.1
    caofref.1
    cA
    inidm
    #
    @6
    @1
    eqidd
    #
    @6
    @2
    eqidd
    #
    ofrfval
    wph
    vw
    cA
    cA
    @1
    @2
    cT
    cA
    cF
    cG
    cV
    cV
    @16
    @17
    caofref.1
    caofref.1
    @18
    @19
    @20
    ofrfval
    3imtr4d
end
