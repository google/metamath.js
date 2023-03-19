include "wceq.mm"
include "cop.mm"
include "opeq1.mm"
include "opeq2.mm"
include "sylan9eq.mm"

theorem opeq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = C /\ B = D ) -> <. A , B >. = <. C , D >. )

  proof
    cA
    cC
    wceq
    cB
    cD
    wceq
    cA
    cB
    cop
    cC
    cB
    cop
    cC
    cD
    cop
    cA
    cC
    cB
    opeq1
    cB
    cD
    cC
    opeq2
    sylan9eq
end
