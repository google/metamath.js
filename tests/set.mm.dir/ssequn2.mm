include "wss.mm"
include "cun.mm"
include "wceq.mm"
include "ssequn1.mm"
include "uncom.mm"
include "eqeq1i.mm"
include "bitri.mm"

theorem ssequn2
  let cA: class A
  let cB: class B


  assert |- ( A C_ B <-> ( B u. A ) = B )

  proof
    cA
    cB
    wss
    cA
    cB
    cun
    #
    cB
    wceq
    cB
    cA
    cun
    #
    cB
    wceq
    cA
    cB
    ssequn1
    @0
    @1
    cB
    cA
    cB
    uncom
    eqeq1i
    bitri
end
