include "wceq.mm"
include "cxp.mm"
include "xpeq2.mm"
include "ax-mp.mm"

theorem xpeq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume xpeq1i.1: |- A = B


  assert |- ( C X. A ) = ( C X. B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cxp
    cC
    cB
    cxp
    wceq
    xpeq1i.1
    cA
    cB
    cC
    xpeq2
    ax-mp
end
