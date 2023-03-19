include "cin.mm"
include "cdif.mm"
include "wss.mm"
include "wceq.mm"
include "inss1.mm"
include "dfss4.mm"
include "mpbi.mm"
include "difin.mm"
include "difeq2i.mm"
include "eqtr3i.mm"

theorem dfin4
  let cA: class A
  let cB: class B


  assert |- ( A i^i B ) = ( A \ ( A \ B ) )

  proof
    cA
    cA
    cA
    cB
    cin
    #
    cdif
    #
    cdif
    #
    @0
    cA
    cA
    cB
    cdif
    #
    cdif
    @0
    cA
    wss
    @2
    @0
    wceq
    cA
    cB
    inss1
    @0
    cA
    dfss4
    mpbi
    @1
    @3
    cA
    cA
    cB
    difin
    difeq2i
    eqtr3i
end
