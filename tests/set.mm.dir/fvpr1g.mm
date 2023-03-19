include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "cpr.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "cun.mm"
include "df-pr.mm"
include "fveq1i.mm"
include "necom.mm"
include "fvunsn.mm"
include "sylbi.mm"
include "syl5eq.mm"
include "3ad2ant3.mm"
include "fvsng.mm"
include "3adant3.mm"
include "eqtrd.mm"

theorem fvpr1g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ C e. W /\ A =/= B ) -> ( { <. A , C >. , <. B , D >. } ` A ) = C )

  proof
    cA
    cV
    wcel
    #
    cC
    cW
    wcel
    #
    cA
    cB
    wne
    #
    w3a
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
    @3
    csn
    #
    cfv
    #
    cC
    @2
    @0
    @6
    @8
    wceq
    @1
    @2
    @6
    cA
    @7
    @4
    csn
    cun
    #
    cfv
    #
    @8
    cA
    @5
    @9
    @3
    @4
    df-pr
    fveq1i
    @2
    cB
    cA
    wne
    @10
    @8
    wceq
    cA
    cB
    necom
    @7
    cB
    cD
    cA
    fvunsn
    sylbi
    syl5eq
    3ad2ant3
    @0
    @1
    @8
    cC
    wceq
    @2
    cA
    cC
    cV
    cW
    fvsng
    3adant3
    eqtrd
end
