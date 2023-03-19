include "wceq.mm"
include "cin.mm"
include "ineq2.mm"
include "ax-mp.mm"

theorem ineq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume ineq1i.1: |- A = B


  assert |- ( C i^i A ) = ( C i^i B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cin
    cC
    cB
    cin
    wceq
    ineq1i.1
    cA
    cB
    cC
    ineq2
    ax-mp
end
