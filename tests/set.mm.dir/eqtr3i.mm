include "eqcomi.mm"
include "eqtri.mm"

theorem eqtr3i
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqtr3i.1: |- A = B
  assume eqtr3i.2: |- A = C


  assert |- B = C

  proof
    cB
    cA
    cC
    cA
    cB
    eqtr3i.1
    eqcomi
    eqtr3i.2
    eqtri
end
