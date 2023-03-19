include "cin.mm"
include "wceq.mm"
include "ineqcom.mm"
include "mpbi.mm"

theorem ineqcomi
  let cA: class A
  let cB: class B
  let cC: class C
  assume ineqcomi.1: |- ( A i^i B ) = C


  assert |- ( B i^i A ) = C

  proof
    cA
    cB
    cin
    cC
    wceq
    cB
    cA
    cin
    cC
    wceq
    ineqcomi.1
    cA
    cB
    cC
    ineqcom
    mpbi
end
