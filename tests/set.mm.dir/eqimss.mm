include "wceq.mm"
include "wss.mm"
include "eqss.mm"
include "simplbi.mm"

theorem eqimss
  let cA: class A
  let cB: class B


  assert |- ( A = B -> A C_ B )

  proof
    cA
    cB
    wceq
    cA
    cB
    wss
    cB
    cA
    wss
    cA
    cB
    eqss
    simplbi
end
