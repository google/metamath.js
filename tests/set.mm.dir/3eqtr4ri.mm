include "eqtr4i.mm"

theorem 3eqtr4ri
  param cA: class A
  param cB: class B
  param cC: class C
  param cD: class D
  assume 3eqtr4i.1: |- A = B
  assume 3eqtr4i.2: |- C = A
  assume 3eqtr4i.3: |- D = B


  assert |- D = C

  proof
    cD
    cA
    cC
    cD
    cB
    cA
    3eqtr4i.3
    3eqtr4i.1
    eqtr4i
    3eqtr4i.2
    eqtr4i
end
