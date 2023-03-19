include "wceq.mm"
include "ciin.mm"
include "iineq1.mm"
include "syl.mm"

theorem iineq1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iineq1d.1: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  assert |- ( ph -> |^|_ x e. A C = |^|_ x e. B C )

  proof
    wph
    cA
    cB
    wceq
    vx
    cA
    cC
    ciin
    vx
    cB
    cC
    ciin
    wceq
    iineq1d.1
    vx
    cA
    cB
    cC
    iineq1
    syl
end
