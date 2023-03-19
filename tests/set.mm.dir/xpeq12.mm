include "wceq.mm"
include "cxp.mm"
include "xpeq1.mm"
include "xpeq2.mm"
include "sylan9eq.mm"

theorem xpeq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> ( A X. C ) = ( B X. D ) )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cxp
    cB
    cC
    cxp
    cB
    cD
    cxp
    cA
    cB
    cC
    xpeq1
    cC
    cD
    cB
    xpeq2
    sylan9eq
end
