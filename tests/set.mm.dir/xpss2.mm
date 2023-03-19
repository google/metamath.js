include "wss.mm"
include "cxp.mm"
include "ssid.mm"
include "xpss12.mm"
include "mpan.mm"

theorem xpss2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A C_ B -> ( C X. A ) C_ ( C X. B ) )

  proof
    cC
    cC
    wss
    cA
    cB
    wss
    cC
    cA
    cxp
    cC
    cB
    cxp
    wss
    cC
    ssid
    cC
    cC
    cA
    cB
    xpss12
    mpan
end
