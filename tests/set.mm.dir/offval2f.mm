include "cof.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "wfn.mm"
include "wcel.mm"
include "wral.mm"
include "ex.mm"
include "ralrimi.mm"
include "fnmptf.mm"
include "syl.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "inidm.mm"
include "wa.mm"
include "wceq.mm"
include "adantr.mm"
include "fveq1d.mm"
include "offval.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfov.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "cbvmptf.mm"
include "simpr.mm"
include "fvmpt2f.mm"
include "syl2anc.mm"
include "mpteq2da.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem offval2f
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
  assume offval2f.0: |- F/ x ph
  assume offval2f.a: |- F/_ x A
  assume offval2f.1: |- ( ph -> A e. V )
  assume offval2f.2: |- ( ( ph /\ x e. A ) -> B e. W )
  assume offval2f.3: |- ( ( ph /\ x e. A ) -> C e. X )
  assume offval2f.4: |- ( ph -> F = ( x e. A |-> B ) )
  assume offval2f.5: |- ( ph -> G = ( x e. A |-> C ) )

  disjoint R x
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint F y
  disjoint G y
  disjoint ph y
  disjoint x y
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
    offval2f.0
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @10
    offval2f.2
    ex
    ralrimi
    vx
    cA
    cB
    cW
    offval2f.a
    fnmptf
    syl
    wph
    cA
    cF
    @1
    offval2f.4
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
    @13
    wph
    @14
    vx
    cA
    offval2f.0
    wph
    @12
    @14
    offval2f.3
    ex
    ralrimi
    vx
    cA
    cC
    cX
    offval2f.a
    fnmptf
    syl
    wph
    cA
    cG
    @3
    offval2f.5
    fneq1d
    mpbird
    offval2f.1
    offval2f.1
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
    offval2f.4
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
    offval2f.5
    adantr
    fveq1d
    offval
    wph
    @6
    vx
    cA
    @11
    @1
    cfv
    #
    @11
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
    @19
    vy
    cA
    nfcv
    offval2f.a
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
    @19
    nfcv
    @0
    @11
    wceq
    @2
    @17
    @4
    @18
    cR
    @0
    @11
    @1
    fveq2
    @0
    @11
    @3
    fveq2
    oveq12d
    cbvmptf
    wph
    vx
    cA
    @19
    @7
    offval2f.0
    wph
    @12
    wa
    #
    @17
    cB
    @18
    cC
    cR
    @20
    @12
    @10
    @17
    cB
    wceq
    wph
    @12
    simpr
    #
    offval2f.2
    vx
    cA
    cB
    cW
    offval2f.a
    fvmpt2f
    syl2anc
    @20
    @12
    @14
    @18
    cC
    wceq
    @21
    offval2f.3
    vx
    cA
    cC
    cX
    offval2f.a
    fvmpt2f
    syl2anc
    oveq12d
    mpteq2da
    syl5eq
    eqtrd
end
