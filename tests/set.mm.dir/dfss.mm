include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "df-ss.mm"
include "eqcom.mm"
include "bitri.mm"

theorem dfss
  let cA: class A
  let cB: class B


  assert |- ( A C_ B <-> A = ( A i^i B ) )

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
    cA
    @0
    wceq
    cA
    cB
    df-ss
    @0
    cA
    eqcom
    bitri
end
