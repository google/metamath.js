include "cof.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "cin.mm"
include "inss1.mm"
include "eqsstr3i.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "inss2.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "eqidd.mm"
include "offval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem off
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vz: setvar z
  assume off.1: |- ( ( ph /\ ( x e. S /\ y e. T ) ) -> ( x R y ) e. U )
  assume off.2: |- ( ph -> F : A --> S )
  assume off.3: |- ( ph -> G : B --> T )
  assume off.4: |- ( ph -> A e. V )
  assume off.5: |- ( ph -> B e. W )
  assume off.6: |- ( A i^i B ) = C

  disjoint G y
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint U y
  disjoint A z
  disjoint C z
  disjoint y z
  disjoint G z
  disjoint x z
  disjoint ph z
  disjoint F z
  disjoint R z
  disjoint U z
  assert |- ( ph -> ( F oF R G ) : C --> U )

  proof
    wph
    cC
    cU
    cF
    cG
    cR
    cof
    co
    #
    wf
    cC
    cU
    vz
    cC
    vz
    cv
    #
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    #
    wf
    wph
    vz
    cC
    @4
    cU
    @5
    wph
    @1
    cC
    wcel
    #
    wa
    @2
    cS
    wcel
    #
    @3
    cT
    wcel
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
    @4
    cU
    wcel
    #
    wph
    cA
    cS
    cF
    wf
    #
    @1
    cA
    wcel
    #
    @7
    @6
    off.2
    cC
    cA
    @1
    cC
    cA
    cB
    cin
    #
    cA
    off.6
    cA
    cB
    inss1
    eqsstr3i
    sseli
    cA
    cS
    @1
    cF
    ffvelrn
    syl2an
    wph
    cB
    cT
    cG
    wf
    #
    @1
    cB
    wcel
    #
    @8
    @6
    off.3
    cC
    cB
    @1
    cC
    @17
    cB
    off.6
    cA
    cB
    inss2
    eqsstr3i
    sseli
    cB
    cT
    @1
    cG
    ffvelrn
    syl2an
    wph
    @13
    @6
    wph
    @12
    vx
    vy
    cS
    cT
    off.1
    ralrimivva
    adantr
    @12
    @14
    @2
    @10
    cR
    co
    #
    cU
    wcel
    vx
    vy
    @2
    @3
    cS
    cT
    @9
    @2
    wceq
    @11
    @20
    cU
    @9
    @2
    @10
    cR
    oveq1
    eleq1d
    @10
    @3
    wceq
    @20
    @4
    cU
    @10
    @3
    @2
    cR
    oveq2
    eleq1d
    rspc2va
    syl21anc
    @5
    eqid
    fmptd
    wph
    cC
    cU
    @0
    @5
    wph
    vz
    cA
    cB
    @2
    @3
    cR
    cC
    cF
    cG
    cV
    cW
    wph
    @15
    cF
    cA
    wfn
    off.2
    cA
    cS
    cF
    ffn
    syl
    wph
    @18
    cG
    cB
    wfn
    off.3
    cB
    cT
    cG
    ffn
    syl
    off.4
    off.5
    off.6
    wph
    @16
    wa
    @2
    eqidd
    wph
    @19
    wa
    @3
    eqidd
    offval
    feq1d
    mpbird
end
