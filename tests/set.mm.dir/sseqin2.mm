include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "df-ss.mm"
include "incom.mm"
include "eqeq1i.mm"
include "bitri.mm"

theorem sseqin2
  let cA: class A
  let cB: class B


  assert |- ( A C_ B <-> ( B i^i A ) = A )

  proof
    cA
    cB
    wss
    cA
    cB
    cin
    #
    cA
    wceq
    cB
    cA
    cin
    #
    cA
    wceq
    cA
    cB
    df-ss
    @0
    @1
    cA
    cA
    cB
    incom
    eqeq1i
    bitri
end
