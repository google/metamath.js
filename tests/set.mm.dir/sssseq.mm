include "wceq.mm"
include "wss.mm"
include "eqss.mm"
include "rbaibr.mm"

theorem sssseq
  let cA: class A
  let cB: class B


  assert |- ( B C_ A -> ( A C_ B <-> A = B ) )

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
    rbaibr
end
