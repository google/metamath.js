include "cvv.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "ssv.mm"
include "biantrur.mm"
include "eqss.mm"
include "bitr4i.mm"

theorem vss
  let cA: class A


  assert |- ( _V C_ A <-> A = _V )

  proof
    cvv
    cA
    wss
    #
    cA
    cvv
    wss
    #
    @0
    wa
    cA
    cvv
    wceq
    @1
    @0
    cA
    ssv
    biantrur
    cA
    cvv
    eqss
    bitr4i
end
