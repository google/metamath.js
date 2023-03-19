include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "cmpt.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem fmpt2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  assume fmpt2d.2: |- ( ( ph /\ x e. A ) -> B e. V )
  assume fmpt2d.1: |- ( ph -> F = ( x e. A |-> B ) )
  assume fmpt2d.3: |- ( ( ph /\ y e. A ) -> ( F ` y ) e. C )

  disjoint A x
  disjoint A y
  disjoint C y
  disjoint F y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> F : A --> C )

  proof
    wph
    cF
    cA
    wfn
    #
    vy
    cv
    cF
    cfv
    cC
    wcel
    #
    vy
    cA
    wral
    cA
    cC
    cF
    wf
    wph
    @0
    vx
    cA
    cB
    cmpt
    #
    cA
    wfn
    #
    wph
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    @3
    wph
    @4
    vx
    cA
    fmpt2d.2
    ralrimiva
    vx
    cA
    cB
    @2
    cV
    @2
    eqid
    fnmpt
    syl
    wph
    cA
    cF
    @2
    fmpt2d.1
    fneq1d
    mpbird
    wph
    @1
    vy
    cA
    fmpt2d.3
    ralrimiva
    vy
    cA
    cC
    cF
    ffnfv
    sylanbrc
end
