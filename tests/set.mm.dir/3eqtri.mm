include "eqtri.mm"

theorem 3eqtri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtri.1: |- A = B
  assume 3eqtri.2: |- B = C
  assume 3eqtri.3: |- C = D


  assert |- A = D

  proof
    cA
    cB
    cD
    3eqtri.1
    cB
    cC
    cD
    3eqtri.2
    3eqtri.3
    eqtri
    eqtri
end
