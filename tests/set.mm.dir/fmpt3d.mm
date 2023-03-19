include "wf.mm"
include "cmpt.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem fmpt3d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fmpt3d.1: |- ( ph -> F = ( x e. A |-> B ) )
  assume fmpt3d.2: |- ( ( ph /\ x e. A ) -> B e. C )

  disjoint A x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> F : A --> C )

  proof
    wph
    cA
    cC
    cF
    wf
    cA
    cC
    vx
    cA
    cB
    cmpt
    #
    wf
    wph
    vx
    cA
    cB
    cC
    @0
    fmpt3d.2
    @0
    eqid
    fmptd
    wph
    cA
    cC
    cF
    @0
    fmpt3d.1
    feq1d
    mpbird
end
