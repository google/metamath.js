include "wceq.mm"
include "ccom.mm"
include "coeq1.mm"
include "ax-mp.mm"

theorem coeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume coeq1i.1: |- A = B


  assert |- ( A o. C ) = ( B o. C )

  proof
    cA
    cB
    wceq
    cA
    cC
    ccom
    cB
    cC
    ccom
    wceq
    coeq1i.1
    cA
    cB
    cC
    coeq1
    ax-mp
end
