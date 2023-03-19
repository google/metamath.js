include "nfv.mm"
include "iineq2d.mm"

theorem iineq2dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iuneq2dv.1: |- ( ( ph /\ x e. A ) -> B = C )

  disjoint ph x
  assert |- ( ph -> |^|_ x e. A B = |^|_ x e. A C )

  proof
    wph
    vx
    cA
    cB
    cC
    wph
    vx
    nfv
    iuneq2dv.1
    iineq2d
end
