include "eqtri.mm"
include "eqcomi.mm"

theorem eqtr2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqtr2i.1: |- A = B
  assume eqtr2i.2: |- B = C


  assert |- C = A

  proof
    cA
    cC
    cA
    cB
    cC
    eqtr2i.1
    eqtr2i.2
    eqtri
    eqcomi
end
