include "eleqtri.mm"
include "eqeltrri.mm"

theorem 3eltr3i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eltr3.1: |- A e. B
  assume 3eltr3.2: |- A = C
  assume 3eltr3.3: |- B = D


  assert |- C e. D

  proof
    cA
    cC
    cD
    3eltr3.2
    cA
    cB
    cD
    3eltr3.1
    3eltr3.3
    eleqtri
    eqeltrri
end
