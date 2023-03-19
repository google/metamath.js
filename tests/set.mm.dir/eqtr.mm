include "wceq.mm"
include "eqeq1.mm"
include "biimpar.mm"

theorem eqtr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A = B /\ B = C ) -> A = C )

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
    cA
    cB
    cC
    eqeq1
    biimpar
end
