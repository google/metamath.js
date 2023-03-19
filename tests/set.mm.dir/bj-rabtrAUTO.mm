include "wtru.mm"
include "crab.mm"
include "ssrab2.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "simpl.mm"
include "ssrabdv.mm"
include "trud.mm"
include "eqssi.mm"

theorem bj-rabtrAUTO
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
    wtru
    wtru
    vx
    cA
    cA
    cA
    cA
    wss
    wtru
    cA
    ssid
    a1i
    wtru
    vx
    cv
    cA
    wcel
    simpl
    ssrabdv
    trud
    eqssi
end
