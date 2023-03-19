include "eqcomi.mm"
include "eqnetri.mm"

theorem eqnetrri
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqnetrr.1: |- A = B
  assume eqnetrr.2: |- A =/= C


  assert |- B =/= C

  proof
    cB
    cA
    cC
    cA
    cB
    eqnetrr.1
    eqcomi
    eqnetrr.2
    eqnetri
end
