include "eqcomi.mm"
include "eleqtri.mm"

theorem eleqtrri
  let cA: class A
  let cB: class B
  let cC: class C
  assume eleqtrr.1: |- A e. B
  assume eleqtrr.2: |- C = B


  assert |- A e. C

  proof
    cA
    cB
    cC
    eleqtrr.1
    cC
    cB
    eleqtrr.2
    eqcomi
    eleqtri
end
