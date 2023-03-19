include "wceq.mm"
include "eqcom.mm"
include "mpbi.mm"

theorem eqcomi
  param cA: class A
  param cB: class B
  assume eqcomi.1: |- A = B


  assert |- B = A

  proof
    cA
    cB
    wceq
    cB
    cA
    wceq
    eqcomi.1
    cA
    cB
    eqcom
    mpbi
end
