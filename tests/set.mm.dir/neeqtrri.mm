include "eqcomi.mm"
include "neeqtri.mm"

theorem neeqtrri
  let cA: class A
  let cB: class B
  let cC: class C
  assume neeqtrr.1: |- A =/= B
  assume neeqtrr.2: |- C = B


  assert |- A =/= C

  proof
    cA
    cB
    cC
    neeqtrr.1
    cC
    cB
    neeqtrr.2
    eqcomi
    neeqtri
end
