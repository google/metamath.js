include "wceq.mm"
include "iuneq1d.mm"

theorem bnj1113
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume bnj1113.1: |- ( A = B -> C = D )

  disjoint C x
  disjoint D x
  assert |- ( A = B -> U_ x e. C E = U_ x e. D E )

  proof
    cA
    cB
    wceq
    vx
    cC
    cD
    cE
    bnj1113.1
    iuneq1d
end
