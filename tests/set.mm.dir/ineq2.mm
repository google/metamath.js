include "wceq.mm"
include "cin.mm"
include "ineq1.mm"
include "incom.mm"
include "3eqtr4g.mm"

theorem ineq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( C i^i A ) = ( C i^i B ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    cin
    cB
    cC
    cin
    cC
    cA
    cin
    cC
    cB
    cin
    cA
    cB
    cC
    ineq1
    cC
    cA
    incom
    cC
    cB
    incom
    3eqtr4g
end
