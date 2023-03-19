include "wceq.mm"
include "wral.mm"
include "cixp.mm"
include "ralrimiva.mm"
include "ixpeq2.mm"
include "syl.mm"

theorem ixpeq2dva
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume ixpeq2dva.1: |- ( ( ph /\ x e. A ) -> B = C )

  disjoint ph x
  assert |- ( ph -> X_ x e. A B = X_ x e. A C )

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
    cixp
    vx
    cA
    cC
    cixp
    wceq
    wph
    @0
    vx
    cA
    ixpeq2dva.1
    ralrimiva
    vx
    cA
    cB
    cC
    ixpeq2
    syl
end
