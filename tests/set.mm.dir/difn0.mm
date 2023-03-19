include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "eqimss.mm"
include "ssdif0.mm"
include "sylib.mm"
include "necon3i.mm"

theorem difn0
  let cA: class A
  let cB: class B


  assert |- ( ( A \ B ) =/= (/) -> A =/= B )

  proof
    cA
    cB
    cA
    cB
    cdif
    #
    c0
    cA
    cB
    wceq
    cA
    cB
    wss
    @0
    c0
    wceq
    cA
    cB
    eqimss
    cA
    cB
    ssdif0
    sylib
    necon3i
end
