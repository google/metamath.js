include "wss.mm"
include "eqimss.mm"
include "eqcoms.mm"

theorem eqimss2
  let cA: class A
  let cB: class B


  assert |- ( B = A -> A C_ B )

  proof
    cA
    cB
    wss
    cA
    cB
    cA
    cB
    eqimss
    eqcoms
end
