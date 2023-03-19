include "cof.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "wfn.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "inidm.mm"
include "wa.mm"
include "wceq.mm"
include "adantr.mm"
include "fveq1d.mm"
include "offval.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfov.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "cbvmpt.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem offval2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let vy: setvar y
  assume offval2.1: |- ( ph -> A e. V )
  assume offval2.2: |- ( ( ph /\ x e. A ) -> B e. W )
  assume offval2.3: |- ( ( ph /\ x e. A ) -> C e. X )
  assume offval2.4: |- ( ph -> F = ( x e. A |-> B ) )
  assume offval2.5: |- ( ph -> G = ( x e. A |-> C ) )

  disjoint A x
  disjoint ph x
  disjoint R x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint F y
  disjoint G y
  disjoint ph y
  disjoint R y
  assert |- ( ph -> ( F oF R G ) = ( x e. A |-> ( B R C ) ) )

  proof
    wph
    cF
    cG
    cR
    cof
    co
    vy
    cA
    vy
    cv
    #
    vx
    cA
    cB
    cmpt
    #
    cfv
    #
    @0
    vx
    cA
    cC
    cmpt
    #
    cfv
    #
    cR
    co
    #
    cmpt
    #
    vx
    cA
    cB
    cC
    cR
    co
    #
    cmpt
    #
    wph
    vy
    cA
    cA
    @2
    @4
    cR
    cA
    cF
    cG
    cV
    cV
    wph
    cF
    cA
    wfn
    @1
    cA
    wfn
    #
    wph
    cB
    cW
    wcel
    #
    vx
    cA
    wral
    @9
    wph
    @10
    vx
    cA
    offval2.2
    ralrimiva
    vx
    cA
    cB
    @1
    cW
    @1
    eqid
    #
    fnmpt
    syl
    wph
    cA
    cF
    @1
    offval2.4
    fneq1d
    mpbird
    wph
    cG
    cA
    wfn
    @3
    cA
    wfn
    #
    wph
    cC
    cX
    wcel
    #
    vx
    cA
    wral
    @12
    wph
    @13
    vx
    cA
    offval2.3
    ralrimiva
    vx
    cA
    cC
    @3
    cX
    @3
    eqid
    #
    fnmpt
    syl
    wph
    cA
    cG
    @3
    offval2.5
    fneq1d
    mpbird
    offval2.1
    offval2.1
    cA
    inidm
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @0
    cF
    @1
    wph
    cF
    @1
    wceq
    @15
    offval2.4
    adantr
    fveq1d
    @16
    @0
    cG
    @3
    wph
    cG
    @3
    wceq
    @15
    offval2.5
    adantr
    fveq1d
    offval
    wph
    @6
    vx
    cA
    vx
    cv
    #
    @1
    cfv
    #
    @17
    @3
    cfv
    #
    cR
    co
    #
    cmpt
    @8
    vy
    vx
    cA
    @5
    @20
    vx
    @2
    @4
    cR
    vx
    cA
    cB
    @0
    nffvmpt1
    vx
    cR
    nfcv
    vx
    cA
    cC
    @0
    nffvmpt1
    nfov
    vy
    @20
    nfcv
    @0
    @17
    wceq
    @2
    @18
    @4
    @19
    cR
    @0
    @17
    @1
    fveq2
    @0
    @17
    @3
    fveq2
    oveq12d
    cbvmpt
    wph
    vx
    cA
    @20
    @7
    wph
    @17
    cA
    wcel
    #
    wa
    #
    @18
    cB
    @19
    cC
    cR
    @22
    @21
    @10
    @18
    cB
    wceq
    wph
    @21
    simpr
    #
    offval2.2
    vx
    cA
    cB
    cW
    @1
    @11
    fvmpt2
    syl2anc
    @22
    @21
    @13
    @19
    cC
    wceq
    @23
    offval2.3
    vx
    cA
    cC
    cX
    @3
    @14
    fvmpt2
    syl2anc
    oveq12d
    mpteq2dva
    syl5eq
    eqtrd
end
