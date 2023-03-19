include "wceq.mm"
include "cxrn.mm"
include "xrneq1.mm"
include "xrneq2.mm"
include "sylan9eq.mm"

theorem xrneq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> ( A |X. C ) = ( B |X. D ) )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cxrn
    cB
    cC
    cxrn
    cB
    cD
    cxrn
    cA
    cB
    cC
    xrneq1
    cC
    cD
    cB
    xrneq2
    sylan9eq
end
