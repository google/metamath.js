include "wceq.mm"
include "wne.mm"
include "neqne.mm"
include "orri.mm"

theorem exmidne
  let cA: class A
  let cB: class B


  assert |- ( A = B \/ A =/= B )

  proof
    cA
    cB
    wceq
    cA
    cB
    wne
    cA
    cB
    neqne
    orri
end
