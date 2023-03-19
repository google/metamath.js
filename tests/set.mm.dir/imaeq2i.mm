include "wceq.mm"
include "cima.mm"
include "imaeq2.mm"
include "ax-mp.mm"

theorem imaeq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume imaeq1i.1: |- A = B


  assert |- ( C " A ) = ( C " B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cima
    cC
    cB
    cima
    wceq
    imaeq1i.1
    cA
    cB
    cC
    imaeq2
    ax-mp
end
