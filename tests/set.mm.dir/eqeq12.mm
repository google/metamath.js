include "wceq.mm"
include "eqeq1.mm"
include "eqeq2.mm"
include "sylan9bb.mm"

theorem eqeq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> ( A = C <-> B = D ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    wceq
    cB
    cC
    wceq
    cC
    cD
    wceq
    cB
    cD
    wceq
    cA
    cB
    cC
    eqeq1
    cC
    cD
    cB
    eqeq2
    sylan9bb
end
