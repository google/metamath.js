include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "uniss.mm"
include "unipw.mm"
include "syl6sseq.mm"

theorem pwuniss
  let cA: class A
  let cB: class B


  assert |- ( A C_ ~P B -> U. A C_ B )

  proof
    cA
    cB
    cpw
    #
    wss
    cA
    cuni
    @0
    cuni
    cB
    cA
    @0
    uniss
    cB
    unipw
    syl6sseq
end
