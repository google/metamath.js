include "wceq.mm"
include "co.mm"
include "oveq1.mm"
include "oveq2.mm"
include "sylan9eq.mm"

theorem oveq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( A = B /\ C = D ) -> ( A F C ) = ( B F D ) )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cF
    co
    cB
    cC
    cF
    co
    cB
    cD
    cF
    co
    cA
    cB
    cC
    cF
    oveq1
    cC
    cD
    cB
    cF
    oveq2
    sylan9eq
end
