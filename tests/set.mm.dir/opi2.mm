include "cpr.mm"
include "csn.mm"
include "cop.mm"
include "prex.mm"
include "prid2.mm"
include "dfop.mm"
include "eleqtrri.mm"

theorem opi2
  let cA: class A
  let cB: class B
  assume opi1.1: |- A e. _V
  assume opi1.2: |- B e. _V


  assert |- { A , B } e. <. A , B >.

  proof
    cA
    cB
    cpr
    #
    cA
    csn
    #
    @0
    cpr
    cA
    cB
    cop
    @1
    @0
    cA
    cB
    prex
    prid2
    cA
    cB
    opi1.1
    opi1.2
    dfop
    eleqtrri
end
