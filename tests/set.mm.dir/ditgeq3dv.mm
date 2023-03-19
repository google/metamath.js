include "wceq.mm"
include "cr.mm"
include "wral.mm"
include "cdit.mm"
include "ralrimiva.mm"
include "ditgeq3.mm"
include "syl.mm"

theorem ditgeq3dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cC: class C
  assume ditgeq3dv.1: |- ( ( ph /\ x e. RR ) -> D = E )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint C x
  assert |- ( ph -> S_ [ A -> B ] D _d x = S_ [ A -> B ] E _d x )

  proof
    wph
    cD
    cE
    wceq
    #
    vx
    cr
    wral
    vx
    cA
    cB
    cD
    cdit
    vx
    cA
    cB
    cE
    cdit
    wceq
    wph
    @0
    vx
    cr
    ditgeq3dv.1
    ralrimiva
    vx
    cA
    cB
    cD
    cE
    ditgeq3
    syl
end
