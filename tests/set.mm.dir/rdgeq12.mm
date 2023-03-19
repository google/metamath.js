include "wceq.mm"
include "crdg.mm"
include "rdgeq2.mm"
include "rdgeq1.mm"
include "sylan9eqr.mm"

theorem rdgeq12
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( F = G /\ A = B ) -> rec ( F , A ) = rec ( G , B ) )

  proof
    cA
    cB
    wceq
    cF
    cG
    wceq
    cF
    cA
    crdg
    cF
    cB
    crdg
    cG
    cB
    crdg
    cA
    cB
    cF
    rdgeq2
    cB
    cF
    cG
    rdgeq1
    sylan9eqr
end
