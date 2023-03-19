include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "elpri.mm"
include "cvv.mm"
include "wb.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "elprg.mm"
include "syl.mm"
include "ibir.mm"
include "impbii.mm"

theorem elpr2OLD
  let cA: class A
  let cB: class B
  let cC: class C
  assume elpr2.1: |- B e. _V
  assume elpr2.2: |- C e. _V


  assert |- ( A e. { B , C } <-> ( A = B \/ A = C ) )

  proof
    cA
    cB
    cC
    cpr
    wcel
    #
    cA
    cB
    wceq
    #
    cA
    cC
    wceq
    #
    wo
    #
    cA
    cB
    cC
    elpri
    @3
    @0
    @3
    cA
    cvv
    wcel
    #
    @0
    @3
    wb
    @1
    @4
    @2
    @1
    @4
    cB
    cvv
    wcel
    elpr2.1
    cA
    cB
    cvv
    eleq1
    mpbiri
    @2
    @4
    cC
    cvv
    wcel
    elpr2.2
    cA
    cC
    cvv
    eleq1
    mpbiri
    jaoi
    cA
    cB
    cC
    cvv
    elprg
    syl
    ibir
    impbii
end
