include "cdc.mm"
include "deceq1i.mm"
include "deceq2i.mm"
include "eqtri.mm"

theorem deceq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume deceq1i.1: |- A = B
  assume deceq12i.2: |- C = D


  assert |- ; A C = ; B D

  proof
    cA
    cC
    cdc
    cB
    cC
    cdc
    cB
    cD
    cdc
    cA
    cB
    cC
    deceq1i.1
    deceq1i
    cC
    cD
    cB
    deceq12i.2
    deceq2i
    eqtri
end
