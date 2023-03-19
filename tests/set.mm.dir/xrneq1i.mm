include "wceq.mm"
include "cxrn.mm"
include "xrneq1.mm"
include "ax-mp.mm"

theorem xrneq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume xrneq1i.1: |- A = B


  assert |- ( A |X. C ) = ( B |X. C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cxrn
    cB
    cC
    cxrn
    wceq
    xrneq1i.1
    cA
    cB
    cC
    xrneq1
    ax-mp
end
