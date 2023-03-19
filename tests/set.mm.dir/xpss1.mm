include "wss.mm"
include "cxp.mm"
include "ssid.mm"
include "xpss12.mm"
include "mpan2.mm"

theorem xpss1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A C_ B -> ( A X. C ) C_ ( B X. C ) )

  proof
    cA
    cB
    wss
    cC
    cC
    wss
    cA
    cC
    cxp
    cB
    cC
    cxp
    wss
    cC
    ssid
    cA
    cB
    cC
    cC
    xpss12
    mpan2
end
