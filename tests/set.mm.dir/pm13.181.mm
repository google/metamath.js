include "wceq.mm"
include "wne.mm"
include "eqcom.mm"
include "pm13.18.mm"
include "sylanb.mm"

theorem pm13.181
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A = B /\ B =/= C ) -> A =/= C )

  proof
    cA
    cB
    wceq
    cB
    cA
    wceq
    cB
    cC
    wne
    cA
    cC
    wne
    cA
    cB
    eqcom
    cB
    cA
    cC
    pm13.18
    sylanb
end
