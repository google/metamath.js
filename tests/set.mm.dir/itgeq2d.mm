include "wceq.mm"
include "wral.mm"
include "citg.mm"
include "ralrimiva.mm"
include "itgeq2.mm"
include "syl.mm"

theorem itgeq2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume itgeq2d.1: |- ( ( ph /\ x e. A ) -> B = C )

  disjoint ph x
  disjoint k x
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
    itgeq2d.1
    ralrimiva
    vx
    cA
    cB
    cC
    itgeq2
    syl
end
