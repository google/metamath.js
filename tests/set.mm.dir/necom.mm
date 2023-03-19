include "eqcom.mm"
include "necon3bii.mm"

theorem necom
  let cA: class A
  let cB: class B


  assert |- ( A =/= B <-> B =/= A )

  proof
    cA
    cB
    cB
    cA
    cA
    cB
    eqcom
    necon3bii
end
