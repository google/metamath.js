include "eqtr3i.mm"

theorem 3eqtr3ri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 3eqtr3i.1: |- A = B
  assume 3eqtr3i.2: |- A = C
  assume 3eqtr3i.3: |- B = D


  assert |- D = C

  proof
    cB
    cD
    cC
    3eqtr3i.3
    cA
    cB
    cC
    3eqtr3i.1
    3eqtr3i.2
    eqtr3i
    eqtr3i
end
