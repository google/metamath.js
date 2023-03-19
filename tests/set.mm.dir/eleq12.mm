include "wceq.mm"
include "wcel.mm"
include "eleq1.mm"
include "eleq2.mm"
include "sylan9bb.mm"

theorem eleq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> ( A e. C <-> B e. D ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    wcel
    cB
    cC
    wcel
    cC
    cD
    wceq
    cB
    cD
    wcel
    cA
    cB
    cC
    eleq1
    cC
    cD
    cB
    eleq2
    sylan9bb
end
