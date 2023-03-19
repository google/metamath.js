include "cvv.mm"
include "wss.mm"
include "cxp.mm"
include "ssv.mm"
include "xpss12.mm"
include "mp2an.mm"

theorem xpss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( A X. B ) C_ ( _V X. _V )

  proof
    cA
    cvv
    wss
    cB
    cvv
    wss
    cA
    cB
    cxp
    cvv
    cvv
    cxp
    wss
    cA
    ssv
    cB
    ssv
    cA
    cvv
    cB
    cvv
    xpss12
    mp2an
end
