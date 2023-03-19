include "eqtr4i.mm"

theorem 3eqtr4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtr4i.1: |- A = B
  assume 3eqtr4i.2: |- C = A
  assume 3eqtr4i.3: |- D = B


  assert |- C = D

  proof
    cC
    cA
    cD
    3eqtr4i.2
    cD
    cB
    cA
    3eqtr4i.3
    3eqtr4i.1
    eqtr4i
    eqtr4i
end
