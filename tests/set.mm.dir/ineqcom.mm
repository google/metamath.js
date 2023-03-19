include "cin.mm"
include "incom.mm"
include "eqeq1i.mm"

theorem ineqcom
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) = C <-> ( B i^i A ) = C )

  proof
    cA
    cB
    cin
    cB
    cA
    cin
    cC
    cA
    cB
    incom
    eqeq1i
end
