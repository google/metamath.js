include "wceq.mm"
include "wss.mm"
include "eqss.mm"
include "mpbir2an.mm"

theorem eqssi
  let cA: class A
  let cB: class B
  assume eqssi.1: |- A C_ B
  assume eqssi.2: |- B C_ A


  assert |- A = B

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
    eqssi.1
    eqssi.2
    cA
    cB
    eqss
    mpbir2an
end
