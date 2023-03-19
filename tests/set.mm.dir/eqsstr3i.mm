include "eqcomi.mm"
include "eqsstri.mm"

theorem eqsstr3i
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqsstr3.1: |- B = A
  assume eqsstr3.2: |- B C_ C


  assert |- A C_ C

  proof
    cA
    cB
    cC
    cB
    cA
    eqsstr3.1
    eqcomi
    eqsstr3.2
    eqsstri
end
