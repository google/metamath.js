include "eqtri.mm"
include "eqtr2i.mm"

theorem 3eqtrri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtri.1: |- A = B
  assume 3eqtri.2: |- B = C
  assume 3eqtri.3: |- C = D


  assert |- D = A

  proof
    cA
    cC
    cD
    cA
    cB
    cC
    3eqtri.1
    3eqtri.2
    eqtri
    3eqtri.3
    eqtr2i
end
