include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "ralrimiva.mm"
include "fmpt.mm"
include "sylib.mm"

theorem fmptd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fmptd.1: |- ( ( ph /\ x e. A ) -> B e. C )
  assume fmptd.2: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> F : A --> C )

  proof
    wph
    cB
    cC
    wcel
    #
    vx
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
    fmptd.1
    ralrimiva
    vx
    cA
    cC
    cB
    cF
    fmptd.2
    fmpt
    sylib
end
