include "wceq.mm"
include "cin.mm"
include "ineq1.mm"
include "ax-mp.mm"

theorem ineq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume ineq1i.1: |- A = B


  assert |- ( A i^i C ) = ( B i^i C )

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
    wceq
    ineq1i.1
    cA
    cB
    cC
    ineq1
    ax-mp
end
