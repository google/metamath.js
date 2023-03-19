include "cofr.mm"
include "wbr.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "wral.mm"
include "wfn.mm"
include "wcel.mm"
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
include "ofrfval.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfv.mm"
include "fveq2.mm"
include "breq12d.mm"
include "cbvral.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem ofrfval2
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
  assert |- ( ph -> ( F oR R G <-> A. x e. A B R C ) )

  proof
    wph
    cF
    cG
    cR
    cofr
    wbr
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
    wbr
    #
    vy
    cA
    wral
    #
    cB
    cC
    cR
    wbr
    #
    vx
    cA
    wral
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
    ofrfval
    @6
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
    wbr
    #
    vx
    cA
    wral
    wph
    @8
    @5
    @20
    vy
    vx
    cA
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
    nfbr
    @20
    vy
    nfv
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
    breq12d
    cbvral
    wph
    @20
    @7
    vx
    cA
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
    breq12d
    ralbidva
    syl5bb
    bitrd
end
