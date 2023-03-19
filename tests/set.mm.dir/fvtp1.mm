include "wne.mm"
include "wa.mm"
include "cop.mm"
include "ctp.mm"
include "cfv.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "fveq1i.mm"
include "wceq.mm"
include "necom.mm"
include "fvunsn.mm"
include "sylbi.mm"
include "fvpr1.mm"
include "sylan9eqr.mm"
include "syl5eq.mm"

theorem fvtp1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume fvtp1.1: |- A e. _V
  assume fvtp1.4: |- D e. _V


  assert |- ( ( A =/= B /\ A =/= C ) -> ( { <. A , D >. , <. B , E >. , <. C , F >. } ` A ) = D )

  proof
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    wa
    cA
    cA
    cD
    cop
    #
    cB
    cE
    cop
    #
    cC
    cF
    cop
    #
    ctp
    #
    cfv
    cA
    @2
    @3
    cpr
    #
    @4
    csn
    cun
    #
    cfv
    #
    cD
    cA
    @5
    @7
    @2
    @3
    @4
    df-tp
    fveq1i
    @1
    @0
    @8
    cA
    @6
    cfv
    #
    cD
    @1
    cC
    cA
    wne
    @8
    @9
    wceq
    cA
    cC
    necom
    @6
    cC
    cF
    cA
    fvunsn
    sylbi
    cA
    cB
    cD
    cE
    fvtp1.1
    fvtp1.4
    fvpr1
    sylan9eqr
    syl5eq
end
