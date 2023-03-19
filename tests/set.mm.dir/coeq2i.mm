include "wceq.mm"
include "ccom.mm"
include "coeq2.mm"
include "ax-mp.mm"

theorem coeq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume coeq1i.1: |- A = B


  assert |- ( C o. A ) = ( C o. B )

  proof
    cA
    cB
    wceq
    cC
    cA
    ccom
    cC
    cB
    ccom
    wceq
    coeq1i.1
    cA
    cB
    cC
    coeq2
    ax-mp
end
