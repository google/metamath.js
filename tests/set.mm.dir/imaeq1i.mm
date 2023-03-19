include "wceq.mm"
include "cima.mm"
include "imaeq1.mm"
include "ax-mp.mm"

theorem imaeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume imaeq1i.1: |- A = B


  assert |- ( A " C ) = ( B " C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cima
    cB
    cC
    cima
    wceq
    imaeq1i.1
    cA
    cB
    cC
    imaeq1
    ax-mp
end
