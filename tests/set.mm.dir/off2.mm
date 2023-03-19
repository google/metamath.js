include "cof.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "adantr.mm"
include "cin.mm"
include "inss1.mm"
include "syl6eqssr.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "inss2.mm"
include "ralrimivva.mm"
include "ovrspc2v.mm"
include "syl21anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "eqidd.mm"
include "offval.mm"
include "mpteq1d.mm"
include "eqtrd.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem off2
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
  assume off2.1: |- ( ( ph /\ ( x e. S /\ y e. T ) ) -> ( x R y ) e. U )
  assume off2.2: |- ( ph -> F : A --> S )
  assume off2.3: |- ( ph -> G : B --> T )
  assume off2.4: |- ( ph -> A e. V )
  assume off2.5: |- ( ph -> B e. W )
  assume off2.6: |- ( ph -> ( A i^i B ) = C )

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
  disjoint B z
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
    #
    @2
    cS
    wcel
    @3
    cT
    wcel
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
    @4
    cU
    wcel
    @7
    cA
    cS
    @1
    cF
    wph
    cA
    cS
    cF
    wf
    #
    @6
    off2.2
    adantr
    wph
    cC
    cA
    @1
    wph
    cC
    cA
    cB
    cin
    #
    cA
    off2.6
    cA
    cB
    inss1
    syl6eqssr
    sselda
    ffvelrnd
    @7
    cB
    cT
    @1
    cG
    wph
    cB
    cT
    cG
    wf
    #
    @6
    off2.3
    adantr
    wph
    cC
    cB
    @1
    wph
    cC
    @11
    cB
    off2.6
    cA
    cB
    inss2
    syl6eqssr
    sselda
    ffvelrnd
    wph
    @9
    @6
    wph
    @8
    vx
    vy
    cS
    cT
    off2.1
    ralrimivva
    adantr
    vx
    vy
    cS
    cT
    cU
    cR
    @2
    @3
    ovrspc2v
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
    @0
    vz
    @11
    @4
    cmpt
    @5
    wph
    vz
    cA
    cB
    @2
    @3
    cR
    @11
    cF
    cG
    cV
    cW
    wph
    @10
    cF
    cA
    wfn
    off2.2
    cA
    cS
    cF
    ffn
    syl
    wph
    @12
    cG
    cB
    wfn
    off2.3
    cB
    cT
    cG
    ffn
    syl
    off2.4
    off2.5
    @11
    eqid
    wph
    @1
    cA
    wcel
    wa
    @2
    eqidd
    wph
    @1
    cB
    wcel
    wa
    @3
    eqidd
    offval
    wph
    vz
    @11
    cC
    @4
    off2.6
    mpteq1d
    eqtrd
    feq1d
    mpbird
end
