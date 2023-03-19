include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "snssg.mm"
include "ibi.mm"

theorem snssi
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> { A } C_ B )

  proof
    cA
    cB
    wcel
    cA
    csn
    cB
    wss
    cA
    cB
    cB
    snssg
    ibi
end
