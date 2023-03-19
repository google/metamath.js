include "eleqtrri.mm"
include "eqeltri.mm"

theorem 3eltr4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eltr4.1: |- A e. B
  assume 3eltr4.2: |- C = A
  assume 3eltr4.3: |- D = B


  assert |- C e. D

  proof
    cC
    cA
    cD
    3eltr4.2
    cA
    cB
    cD
    3eltr4.1
    3eltr4.3
    eleqtrri
    eqeltri
end
