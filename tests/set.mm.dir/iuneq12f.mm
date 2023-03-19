include "wceq.mm"
include "wral.mm"
include "ciun.mm"
include "iuneq2.mm"
include "iuneq2f.mm"
include "sylan9eqr.mm"

theorem iuneq12f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume iuneq12f.1: |- F/_ x A
  assume iuneq12f.2: |- F/_ x B


  assert |- ( ( A = B /\ A. x e. A C = D ) -> U_ x e. A C = U_ x e. B D )

  proof
    cC
    cD
    wceq
    vx
    cA
    wral
    cA
    cB
    wceq
    vx
    cA
    cC
    ciun
    vx
    cA
    cD
    ciun
    vx
    cB
    cD
    ciun
    vx
    cA
    cC
    cD
    iuneq2
    vx
    cA
    cB
    cD
    iuneq12f.1
    iuneq12f.2
    iuneq2f
    sylan9eqr
end
