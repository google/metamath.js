include "wceq.mm"
include "wss.mm"
include "cin.mm"
include "eqimss.mm"
include "df-ss.mm"
include "sylib.mm"

theorem bnj1322
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( A i^i B ) = A )

  proof
    cA
    cB
    wceq
    cA
    cB
    wss
    cA
    cB
    cin
    cA
    wceq
    cA
    cB
    eqimss
    cA
    cB
    df-ss
    sylib
end
