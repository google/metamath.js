include "wceq.mm"
include "ciun.mm"
include "iuneq1.mm"
include "ax-mp.mm"

theorem iuneq1i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iuneq1i.1: |- A = B

  disjoint A x
  disjoint B x
  assert |- U_ x e. A C = U_ x e. B C

  proof
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
    iuneq1i.1
    vx
    cA
    cB
    cC
    iuneq1
    ax-mp
end
