include "wceq.mm"
include "eqcom.mm"
include "eqtr.mm"
include "sylanb.mm"

theorem eqtr2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A = B /\ A = C ) -> B = C )

  proof
    cA
    cB
    wceq
    cB
    cA
    wceq
    cA
    cC
    wceq
    cB
    cC
    wceq
    cA
    cB
    eqcom
    cB
    cA
    cC
    eqtr
    sylanb
end
