include "wceq.mm"
include "wcel.mm"
include "eleq1.mm"
include "biimpar.mm"

theorem eqeltr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A = B /\ B e. C ) -> A e. C )

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
    cA
    cB
    cC
    eleq1
    biimpar
end
