include "wceq.mm"
include "cun.mm"
include "uneq1.mm"
include "uneq2.mm"
include "sylan9eq.mm"

theorem uneq12
  param cA: class A
  param cB: class B
  param cC: class C
  param cD: class D


  assert |- ( ( A = B /\ C = D ) -> ( A u. C ) = ( B u. D ) )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cun
    cB
    cC
    cun
    cB
    cD
    cun
    cA
    cB
    cC
    uneq1
    cC
    cD
    cB
    uneq2
    sylan9eq
end
