include "cvv.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cdif.mm"
include "wb.mm"
include "ssv.mm"
include "reldisj.mm"
include "ax-mp.mm"

theorem disj2
  let cA: class A
  let cB: class B


  assert |- ( ( A i^i B ) = (/) <-> A C_ ( _V \ B ) )

  proof
    cA
    cvv
    wss
    cA
    cB
    cin
    c0
    wceq
    cA
    cvv
    cB
    cdif
    wss
    wb
    cA
    ssv
    cA
    cB
    cvv
    reldisj
    ax-mp
end
