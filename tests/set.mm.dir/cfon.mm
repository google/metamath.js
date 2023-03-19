include "ccf.mm"
include "cfv.mm"
include "ccrd.mm"
include "con0.mm"
include "cardcf.mm"
include "cardon.mm"
include "eqeltrri.mm"

theorem cfon
  let cA: class A


  assert |- ( cf ` A ) e. On

  proof
    cA
    ccf
    cfv
    #
    ccrd
    cfv
    @0
    con0
    cA
    cardcf
    @0
    cardon
    eqeltrri
end
