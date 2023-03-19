include "wcel.mm"
include "cssr.mm"
include "wbr.mm"
include "wss.mm"
include "ssid.mm"
include "brssr.mm"
include "mpbiri.mm"

theorem brssrid
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A _S A )

  proof
    cA
    cV
    wcel
    cA
    cA
    cssr
    wbr
    cA
    cA
    wss
    cA
    ssid
    cA
    cA
    cV
    brssr
    mpbiri
end
