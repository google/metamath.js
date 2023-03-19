include "wtru.mm"
include "crab.mm"
include "ssrab2.mm"
include "wss.mm"
include "wral.mm"
include "ssid.mm"
include "tru.mm"
include "rgenw.mm"
include "ssrab.mm"
include "mpbir2an.mm"
include "eqssi.mm"

theorem bj-rabtr
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- { x e. A | T. } = A

  proof
    wtru
    vx
    cA
    crab
    #
    cA
    wtru
    vx
    cA
    ssrab2
    cA
    @0
    wss
    cA
    cA
    wss
    wtru
    vx
    cA
    wral
    cA
    ssid
    wtru
    vx
    cA
    tru
    rgenw
    wtru
    vx
    cA
    cA
    ssrab
    mpbir2an
    eqssi
end
