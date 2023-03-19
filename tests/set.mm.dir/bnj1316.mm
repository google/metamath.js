include "wceq.mm"
include "nfcii.mm"
include "nfeq.mm"
include "nf5ri.mm"
include "bnj956.mm"

theorem bnj1316
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume bnj1316.1: |- ( y e. A -> A. x y e. A )
  assume bnj1316.2: |- ( y e. B -> A. x y e. B )

  disjoint A y
  disjoint B y
  disjoint x y
  assert |- ( A = B -> U_ x e. A C = U_ x e. B C )

  proof
    vx
    cA
    cB
    cC
    cA
    cB
    wceq
    vx
    vx
    cA
    cB
    vx
    vy
    cA
    bnj1316.1
    nfcii
    vx
    vy
    cB
    bnj1316.2
    nfcii
    nfeq
    nf5ri
    bnj956
end
