include "wcel.mm"
include "cssr.mm"
include "ccnv.mm"
include "wbr.mm"
include "wss.mm"
include "ssid.mm"
include "brcnvssr.mm"
include "mpbiri.mm"

theorem brcnvssrid
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A `' _S A )

  proof
    cA
    cV
    wcel
    cA
    cA
    cssr
    ccnv
    wbr
    cA
    cA
    wss
    cA
    ssid
    cA
    cA
    cV
    brcnvssr
    mpbiri
end
