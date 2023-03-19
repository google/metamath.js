include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "ssid.mm"
include "uniopn.mm"
include "mpan2.mm"
include "syl5eqel.mm"

theorem topopn
  let cJ: class J
  let cX: class X
  let cA: class A
  let vx: setvar x
  assume 1open.1: |- X = U. J


  assert |- ( J e. Top -> X e. J )

  proof
    cJ
    ctop
    wcel
    #
    cX
    cJ
    cuni
    #
    cJ
    1open.1
    @0
    cJ
    cJ
    wss
    @1
    cJ
    wcel
    cJ
    ssid
    cJ
    cJ
    uniopn
    mpan2
    syl5eqel
end
