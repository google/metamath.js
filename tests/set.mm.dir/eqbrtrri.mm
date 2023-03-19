include "eqcomi.mm"
include "eqbrtri.mm"

theorem eqbrtrri
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume eqbrtrr.1: |- A = B
  assume eqbrtrr.2: |- A R C


  assert |- B R C

  proof
    cB
    cA
    cC
    cR
    cA
    cB
    eqbrtrr.1
    eqcomi
    eqbrtrr.2
    eqbrtri
end
