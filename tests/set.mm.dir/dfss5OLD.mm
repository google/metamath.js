include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "sseqin2.mm"
include "eqcom.mm"
include "bitri.mm"

theorem dfss5OLD
  let cA: class A
  let cB: class B


  assert |- ( A C_ B <-> A = ( B i^i A ) )

  proof
    cA
    cB
    wss
    cB
    cA
    cin
    #
    cA
    wceq
    cA
    @0
    wceq
    cA
    cB
    sseqin2
    @0
    cA
    eqcom
    bitri
end
