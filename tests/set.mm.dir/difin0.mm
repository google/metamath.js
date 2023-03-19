include "cin.mm"
include "wss.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "inss2.mm"
include "ssdif0.mm"
include "mpbi.mm"

theorem difin0
  let cA: class A
  let cB: class B


  assert |- ( ( A i^i B ) \ B ) = (/)

  proof
    cA
    cB
    cin
    #
    cB
    wss
    @0
    cB
    cdif
    c0
    wceq
    cA
    cB
    inss2
    @0
    cB
    ssdif0
    mpbi
end
