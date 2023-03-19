include "wss.mm"
include "wcel.mm"
include "cuni.mm"
include "ssid.mm"
include "ssuni.mm"
include "mpan.mm"

theorem elssuni
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> A C_ U. B )

  proof
    cA
    cA
    wss
    cA
    cB
    wcel
    cA
    cB
    cuni
    wss
    cA
    ssid
    cA
    cA
    cB
    ssuni
    mpan
end
