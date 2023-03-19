include "wne.mm"
include "cop.mm"
include "cpr.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "fveq1i.mm"
include "wceq.mm"
include "necom.mm"
include "fvunsn.mm"
include "sylbi.mm"
include "syl5eq.mm"
include "fvsn.mm"
include "syl6eq.mm"

theorem fvpr1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume fvpr1.1: |- A e. _V
  assume fvpr1.2: |- C e. _V


  assert |- ( A =/= B -> ( { <. A , C >. , <. B , D >. } ` A ) = C )

  proof
    cA
    cB
    wne
    #
    cA
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
    #
    cA
    @1
    csn
    #
    cfv
    #
    cC
    @0
    @4
    cA
    @5
    @2
    csn
    cun
    #
    cfv
    #
    @6
    cA
    @3
    @7
    @1
    @2
    df-pr
    fveq1i
    @0
    cB
    cA
    wne
    @8
    @6
    wceq
    cA
    cB
    necom
    @5
    cB
    cD
    cA
    fvunsn
    sylbi
    syl5eq
    cA
    cC
    fvpr1.1
    fvpr1.2
    fvsn
    syl6eq
end
