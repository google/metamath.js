include "wceq.mm"
include "cxp.mm"
include "xpeq1.mm"
include "ax-mp.mm"

theorem xpeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume xpeq1i.1: |- A = B


  assert |- ( A X. C ) = ( B X. C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cxp
    cB
    cC
    cxp
    wceq
    xpeq1i.1
    cA
    cB
    cC
    xpeq1
    ax-mp
end
