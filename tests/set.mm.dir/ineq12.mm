include "wceq.mm"
include "cin.mm"
include "ineq1.mm"
include "ineq2.mm"
include "sylan9eq.mm"

theorem ineq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> ( A i^i C ) = ( B i^i D ) )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cin
    cB
    cC
    cin
    cB
    cD
    cin
    cA
    cB
    cC
    ineq1
    cC
    cD
    cB
    ineq2
    sylan9eq
end
