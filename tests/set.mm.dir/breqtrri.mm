include "eqcomi.mm"
include "breqtri.mm"

theorem breqtrri
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume breqtrr.1: |- A R B
  assume breqtrr.2: |- C = B


  assert |- A R C

  proof
    cA
    cB
    cC
    cR
    breqtrr.1
    cC
    cB
    breqtrr.2
    eqcomi
    breqtri
end
