include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "wb.mm"
include "snssg.mm"
include "ax-mp.mm"

theorem snss
  let cA: class A
  let cB: class B
  assume snss.1: |- A e. _V


  assert |- ( A e. B <-> { A } C_ B )

  proof
    cA
    cvv
    wcel
    cA
    cB
    wcel
    cA
    csn
    cB
    wss
    wb
    snss.1
    cA
    cB
    cvv
    snssg
    ax-mp
end
