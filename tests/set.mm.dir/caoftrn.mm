include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "cofr.mm"
include "wcel.mm"
include "wi.mm"
include "ralrimivvva.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "anbi2d.mm"
include "rspc3v.mm"
include "syl3anc.mm"
include "mpd.mm"
include "ralimdva.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "r19.26.mm"
include "syl6bbr.mm"
include "3imtr4d.mm"

theorem caoftrn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cO: class O
  let cP: class P
  assume caofref.1: |- ( ph -> A e. V )
  assume caofref.2: |- ( ph -> F : A --> S )
  assume caofcom.3: |- ( ph -> G : A --> S )
  assume caofass.4: |- ( ph -> H : A --> S )
  assume caoftrn.5: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x R y /\ y T z ) -> x U z ) )

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
  disjoint U x
  disjoint U y
  disjoint U z
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
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint ph w
  disjoint R w
  disjoint A w
  disjoint S w
  disjoint T w
  disjoint U w
  assert |- ( ph -> ( ( F oR R G /\ G oR T H ) -> F oR U H ) )

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
    @2
    @0
    cH
    cfv
    #
    cT
    wbr
    #
    wa
    #
    vw
    cA
    wral
    #
    @1
    @4
    cU
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
    #
    cG
    cH
    cT
    cofr
    wbr
    #
    wa
    #
    cF
    cH
    cU
    cofr
    wbr
    wph
    @6
    @8
    vw
    cA
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
    wbr
    #
    @15
    vz
    cv
    #
    cT
    wbr
    #
    wa
    #
    @14
    @17
    cU
    wbr
    #
    wi
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
    @6
    @8
    wi
    #
    wph
    @22
    @12
    wph
    @21
    vx
    vy
    vz
    cS
    cS
    cS
    caoftrn.5
    ralrimivvva
    adantr
    @13
    @1
    cS
    wcel
    @2
    cS
    wcel
    @4
    cS
    wcel
    @22
    @23
    wi
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
    cA
    cS
    @0
    cH
    caofass.4
    ffvelrnda
    @21
    @23
    @1
    @15
    cR
    wbr
    #
    @18
    wa
    #
    @1
    @17
    cU
    wbr
    #
    wi
    @3
    @2
    @17
    cT
    wbr
    #
    wa
    #
    @26
    wi
    vx
    vy
    vz
    @1
    @2
    @4
    cS
    cS
    cS
    @14
    @1
    wceq
    #
    @19
    @25
    @20
    @26
    @29
    @16
    @24
    @18
    @14
    @1
    @15
    cR
    breq1
    anbi1d
    @14
    @1
    @17
    cU
    breq1
    imbi12d
    @15
    @2
    wceq
    #
    @25
    @28
    @26
    @30
    @24
    @3
    @18
    @27
    @15
    @2
    @1
    cR
    breq2
    @15
    @2
    @17
    cT
    breq1
    anbi12d
    imbi1d
    @17
    @4
    wceq
    #
    @28
    @6
    @26
    @8
    @31
    @27
    @5
    @3
    @17
    @4
    @2
    cT
    breq2
    anbi2d
    @17
    @4
    @1
    cU
    breq2
    imbi12d
    rspc3v
    syl3anc
    mpd
    ralimdva
    wph
    @11
    @3
    vw
    cA
    wral
    #
    @5
    vw
    cA
    wral
    #
    wa
    @7
    wph
    @9
    @32
    @10
    @33
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
    @13
    @1
    eqidd
    #
    @13
    @2
    eqidd
    #
    ofrfval
    wph
    vw
    cA
    cA
    @2
    @4
    cT
    cA
    cG
    cH
    cV
    cV
    @35
    wph
    cA
    cS
    cH
    wf
    cH
    cA
    wfn
    caofass.4
    cA
    cS
    cH
    ffn
    syl
    #
    caofref.1
    caofref.1
    @36
    @38
    @13
    @4
    eqidd
    #
    ofrfval
    anbi12d
    @3
    @5
    vw
    cA
    r19.26
    syl6bbr
    wph
    vw
    cA
    cA
    @1
    @4
    cU
    cA
    cF
    cH
    cV
    cV
    @34
    @39
    caofref.1
    caofref.1
    @36
    @37
    @40
    ofrfval
    3imtr4d
end
