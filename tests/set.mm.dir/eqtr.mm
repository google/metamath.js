include "wceq.mm"
include "eqeq1.mm"
include "biimpar.mm"

theorem eqtr
  param cA: class A
  param cB: class B
  param cC: class C


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
