include "eqcomi.mm"
include "eqeltri.mm"

theorem eqeltrri
  param cA: class A
  param cB: class B
  param cC: class C
  assume eqeltrr.1: |- A = B
  assume eqeltrr.2: |- A e. C


  assert |- B e. C

  proof
    cB
    cA
    cC
    cA
    cB
    eqeltrr.1
    eqcomi
    eqeltrr.2
    eqeltri
end
