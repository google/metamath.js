include "csn.mm"
include "cpr.mm"
include "cop.mm"
include "snex.mm"
include "prid1.mm"
include "dfop.mm"
include "eleqtrri.mm"

theorem opi1
  let cA: class A
  let cB: class B
  assume opi1.1: |- A e. _V
  assume opi1.2: |- B e. _V


  assert |- { A } e. <. A , B >.

  proof
    cA
    csn
    #
    @0
    cA
    cB
    cpr
    #
    cpr
    cA
    cB
    cop
    @0
    @1
    cA
    snex
    prid1
    cA
    cB
    opi1.1
    opi1.2
    dfop
    eleqtrri
end
