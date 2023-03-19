include "cvv.mm"
include "cin.mm"
include "inss1.mm"
include "ssid.mm"
include "ssv.mm"
include "ssini.mm"
include "eqssi.mm"

theorem inv1
  let cA: class A


  assert |- ( A i^i _V ) = A

  proof
    cA
    cvv
    cin
    cA
    cA
    cvv
    inss1
    cA
    cA
    cvv
    cA
    ssid
    cA
    ssv
    ssini
    eqssi
end
