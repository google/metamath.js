include "wceq.mm"
include "cpr.mm"
include "preq1.mm"
include "preq2.mm"
include "sylan9eq.mm"

theorem preq12
  param cA: class A
  param cB: class B
  param cC: class C
  param cD: class D


  assert |- ( ( A = C /\ B = D ) -> { A , B } = { C , D } )

  proof
    cA
    cC
    wceq
    cB
    cD
    wceq
    cA
    cB
    cpr
    cC
    cB
    cpr
    cC
    cD
    cpr
    cA
    cC
    cB
    preq1
    cB
    cD
    cC
    preq2
    sylan9eq
end
