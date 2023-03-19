include "wceq.mm"
include "ccom.mm"
include "coeq1.mm"
include "coeq2.mm"
include "eqtrd.mm"

theorem coideq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( A o. A ) = ( B o. B ) )

  proof
    cA
    cB
    wceq
    cA
    cA
    ccom
    cB
    cA
    ccom
    cB
    cB
    ccom
    cA
    cB
    cA
    coeq1
    cA
    cB
    cB
    coeq2
    eqtrd
end
