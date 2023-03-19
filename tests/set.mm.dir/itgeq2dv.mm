include "wceq.mm"
include "wral.mm"
include "citg.mm"
include "ralrimiva.mm"
include "itgeq2.mm"
include "syl.mm"

theorem itgeq2dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume itgeq2dv.1: |- ( ( ph /\ x e. A ) -> B = C )

  disjoint ph x
  assert |- ( ph -> S. A B _d x = S. A C _d x )

  proof
    wph
    cB
    cC
    wceq
    #
    vx
    cA
    wral
    vx
    cA
    cB
    citg
    vx
    cA
    cC
    citg
    wceq
    wph
    @0
    vx
    cA
    itgeq2dv.1
    ralrimiva
    vx
    cA
    cB
    cC
    itgeq2
    syl
end
