include "cof.mm"
include "co.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "cfv.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "wfn.mm"
include "wceq.mm"
include "fvex.mm"
include "fnmpti.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "dffn5.mm"
include "sylib.mm"
include "feqmptd.mm"
include "offval2.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "oveq1d.mm"
include "wral.mm"
include "ralrimiva.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"

theorem caofinvl
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vw: setvar w
  let cC: class C
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cO: class O
  let cP: class P
  let cT: class T
  let cU: class U
  assume caofref.1: |- ( ph -> A e. V )
  assume caofref.2: |- ( ph -> F : A --> S )
  assume caofinv.3: |- ( ph -> B e. W )
  assume caofinv.4: |- ( ph -> N : S --> S )
  assume caofinv.5: |- ( ph -> G = ( v e. A |-> ( N ` ( F ` v ) ) ) )
  assume caofinvl.6: |- ( ( ph /\ x e. S ) -> ( ( N ` x ) R x ) = B )

  disjoint A v
  disjoint F v
  disjoint v x
  disjoint N x
  disjoint N v
  disjoint S v
  disjoint ph v
  disjoint B x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint R x
  disjoint S x
  disjoint v w
  disjoint w x
  disjoint B w
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
  assert |- ( ph -> ( G oF R F ) = ( A X. { B } ) )

  proof
    wph
    cG
    cF
    cR
    cof
    co
    #
    vw
    cA
    cB
    cmpt
    #
    cA
    cB
    csn
    cxp
    wph
    @0
    vw
    cA
    vw
    cv
    #
    cG
    cfv
    #
    @2
    cF
    cfv
    #
    cR
    co
    #
    cmpt
    @1
    wph
    vw
    cA
    @3
    @4
    cR
    cG
    cF
    cV
    cS
    cS
    caofref.1
    wph
    cA
    cS
    @2
    cG
    wph
    cA
    cS
    cG
    wf
    cA
    cS
    vv
    cA
    vv
    cv
    #
    cF
    cfv
    #
    cN
    cfv
    #
    cmpt
    #
    wf
    wph
    vv
    cA
    @8
    cS
    @9
    wph
    @6
    cA
    wcel
    #
    wa
    cS
    cS
    @7
    cN
    wph
    cS
    cS
    cN
    wf
    @10
    caofinv.4
    adantr
    wph
    cA
    cS
    @6
    cF
    caofref.2
    ffvelrnda
    ffvelrnd
    @9
    eqid
    #
    fmptd
    wph
    cA
    cS
    cG
    @9
    caofinv.5
    feq1d
    mpbird
    ffvelrnda
    wph
    cA
    cS
    @2
    cF
    caofref.2
    ffvelrnda
    #
    wph
    cG
    cA
    wfn
    #
    cG
    vw
    cA
    @3
    cmpt
    wceq
    wph
    @13
    @9
    cA
    wfn
    vv
    cA
    @8
    @9
    @7
    cN
    fvex
    @11
    fnmpti
    wph
    cA
    cG
    @9
    caofinv.5
    fneq1d
    mpbiri
    vw
    cA
    cG
    dffn5
    sylib
    wph
    vw
    cA
    cS
    cF
    caofref.2
    feqmptd
    offval2
    wph
    vw
    cA
    @5
    cB
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @5
    @4
    cN
    cfv
    #
    @4
    cR
    co
    #
    cB
    @15
    @3
    @16
    @4
    cR
    wph
    @14
    @3
    @2
    @9
    cfv
    @16
    wph
    @2
    cG
    @9
    caofinv.5
    fveq1d
    vv
    @2
    @8
    @16
    cA
    @9
    @6
    @2
    wceq
    @7
    @4
    cN
    @6
    @2
    cF
    fveq2
    fveq2d
    @11
    @4
    cN
    fvex
    fvmpt
    sylan9eq
    oveq1d
    @15
    @4
    cS
    wcel
    vx
    cv
    #
    cN
    cfv
    #
    @18
    cR
    co
    #
    cB
    wceq
    #
    vx
    cS
    wral
    #
    @17
    cB
    wceq
    #
    @12
    wph
    @22
    @14
    wph
    @21
    vx
    cS
    caofinvl.6
    ralrimiva
    adantr
    @21
    @23
    vx
    @4
    cS
    @18
    @4
    wceq
    #
    @20
    @17
    cB
    @24
    @19
    @16
    @18
    @4
    cR
    @18
    @4
    cN
    fveq2
    @24
    id
    oveq12d
    eqeq1d
    rspcva
    syl2anc
    eqtrd
    mpteq2dva
    eqtrd
    vw
    cA
    cB
    fconstmpt
    syl6eqr
end
