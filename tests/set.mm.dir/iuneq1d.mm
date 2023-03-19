include "wceq.mm"
include "ciun.mm"
include "iuneq1.mm"
include "syl.mm"

theorem iuneq1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iuneq1d.1: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  assert |- ( ph -> U_ x e. A C = U_ x e. B C )

  proof
    wph
    cA
    cB
    wceq
    vx
    cA
    cC
    ciun
    vx
    cB
    cC
    ciun
    wceq
    iuneq1d.1
    vx
    cA
    cB
    cC
    iuneq1
    syl
end
