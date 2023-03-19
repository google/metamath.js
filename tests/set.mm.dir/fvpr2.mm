include "wne.mm"
include "cop.mm"
include "cpr.mm"
include "cfv.mm"
include "prcom.mm"
include "fveq1i.mm"
include "wceq.mm"
include "necom.mm"
include "fvpr1.mm"
include "sylbi.mm"
include "syl5eq.mm"

theorem fvpr2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume fvpr2.1: |- B e. _V
  assume fvpr2.2: |- D e. _V


  assert |- ( A =/= B -> ( { <. A , C >. , <. B , D >. } ` B ) = D )

  proof
    cA
    cB
    wne
    #
    cB
    cA
    cC
    cop
    #
    cB
    cD
    cop
    #
    cpr
    #
    cfv
    cB
    @2
    @1
    cpr
    #
    cfv
    #
    cD
    cB
    @3
    @4
    @1
    @2
    prcom
    fveq1i
    @0
    cB
    cA
    wne
    @5
    cD
    wceq
    cA
    cB
    necom
    cB
    cA
    cD
    cC
    fvpr2.1
    fvpr2.2
    fvpr1
    sylbi
    syl5eq
end
