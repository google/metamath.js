include "wceq.mm"
include "wral.mm"
include "ciun.mm"
include "ralrimiva.mm"
include "iuneq2.mm"
include "syl.mm"

theorem iuneq2dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iuneq2dv.1: |- ( ( ph /\ x e. A ) -> B = C )

  disjoint ph x
  assert |- ( ph -> U_ x e. A B = U_ x e. A C )

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
    ciun
    vx
    cA
    cC
    ciun
    wceq
    wph
    @0
    vx
    cA
    iuneq2dv.1
    ralrimiva
    vx
    cA
    cB
    cC
    iuneq2
    syl
end
