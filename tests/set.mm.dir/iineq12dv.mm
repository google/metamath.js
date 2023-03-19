include "ciin.mm"
include "iineq1d.mm"
include "iineq2dv.mm"
include "eqtrd.mm"

theorem iineq12dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume iineq12dv.1: |- ( ph -> A = B )
  assume iineq12dv.2: |- ( ( ph /\ x e. B ) -> C = D )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> |^|_ x e. A C = |^|_ x e. B D )

  proof
    wph
    vx
    cA
    cC
    ciin
    vx
    cB
    cC
    ciin
    vx
    cB
    cD
    ciin
    wph
    vx
    cA
    cB
    cC
    iineq12dv.1
    iineq1d
    wph
    vx
    cB
    cC
    cD
    iineq12dv.2
    iineq2dv
    eqtrd
end
