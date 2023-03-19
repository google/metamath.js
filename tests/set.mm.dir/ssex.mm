include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "df-ss.mm"
include "inex2.mm"
include "eleq1.mm"
include "mpbii.mm"
include "sylbi.mm"

theorem ssex
  let cA: class A
  let cB: class B
  assume ssex.1: |- B e. _V


  assert |- ( A C_ B -> A e. _V )

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
    #
    cA
    cvv
    wcel
    #
    cA
    cB
    df-ss
    @1
    @0
    cvv
    wcel
    @2
    cB
    cA
    ssex.1
    inex2
    @0
    cA
    cvv
    eleq1
    mpbii
    sylbi
end
