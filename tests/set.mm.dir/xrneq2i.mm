include "wceq.mm"
include "cxrn.mm"
include "xrneq2.mm"
include "ax-mp.mm"

theorem xrneq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume xrneq2i.1: |- A = B


  assert |- ( C |X. A ) = ( C |X. B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cxrn
    cC
    cB
    cxrn
    wceq
    xrneq2i.1
    cA
    cB
    cC
    xrneq2
    ax-mp
end
