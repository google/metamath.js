include "cdm.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "cres.mm"
include "df-ss.mm"
include "dmres.mm"
include "eqeq1i.mm"
include "bitr4i.mm"

theorem ssdmres
  let cA: class A
  let cB: class B


  assert |- ( A C_ dom B <-> dom ( B |` A ) = A )

  proof
    cA
    cB
    cdm
    #
    wss
    cA
    @0
    cin
    #
    cA
    wceq
    cB
    cA
    cres
    cdm
    #
    cA
    wceq
    cA
    @0
    df-ss
    @2
    @1
    cA
    cB
    cA
    dmres
    eqeq1i
    bitr4i
end
