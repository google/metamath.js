include "wceq.mm"
include "eqcom.mm"
include "necon3abii.mm"

theorem nesym
  let cA: class A
  let cB: class B


  assert |- ( A =/= B <-> -. B = A )

  proof
    cB
    cA
    wceq
    cA
    cB
    cA
    cB
    eqcom
    necon3abii
end
