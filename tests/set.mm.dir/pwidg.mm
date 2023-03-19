include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "ssid.mm"
include "elpwg.mm"
include "mpbiri.mm"

theorem pwidg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A e. ~P A )

  proof
    cA
    cV
    wcel
    cA
    cA
    cpw
    wcel
    cA
    cA
    wss
    cA
    ssid
    cA
    cA
    cV
    elpwg
    mpbiri
end
