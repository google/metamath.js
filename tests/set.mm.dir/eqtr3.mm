include "wceq.mm"
include "eqcom.mm"
include "eqtr.mm"
include "sylan2b.mm"

theorem eqtr3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A = C /\ B = C ) -> A = B )

  proof
    cB
    cC
    wceq
    cA
    cC
    wceq
    cC
    cB
    wceq
    cA
    cB
    wceq
    cB
    cC
    eqcom
    cA
    cC
    cB
    eqtr
    sylan2b
end
