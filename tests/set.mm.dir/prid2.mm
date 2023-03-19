include "cpr.mm"
include "prid1.mm"
include "prcom.mm"
include "eleqtri.mm"

theorem prid2
  let cA: class A
  let cB: class B
  assume prid2.1: |- B e. _V


  assert |- B e. { A , B }

  proof
    cB
    cB
    cA
    cpr
    cA
    cB
    cpr
    cB
    cA
    prid2.1
    prid1
    cB
    cA
    prcom
    eleqtri
end
