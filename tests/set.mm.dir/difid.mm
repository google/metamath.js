include "wss.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "ssid.mm"
include "ssdif0.mm"
include "mpbi.mm"

theorem difid
  let cA: class A


  assert |- ( A \ A ) = (/)

  proof
    cA
    cA
    wss
    cA
    cA
    cdif
    c0
    wceq
    cA
    ssid
    cA
    cA
    ssdif0
    mpbi
end
