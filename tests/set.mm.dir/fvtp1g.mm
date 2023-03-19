include "wcel.mm"
include "wa.mm"
include "wne.mm"
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
include "ad2antll.mm"
include "fvpr1g.mm"
include "3expa.mm"
include "adantrr.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem fvtp1g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( ( A e. V /\ D e. W ) /\ ( A =/= B /\ A =/= C ) ) -> ( { <. A , D >. , <. B , E >. , <. C , F >. } ` A ) = D )

  proof
    cA
    cV
    wcel
    #
    cD
    cW
    wcel
    #
    wa
    #
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    wa
    wa
    #
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
    @6
    @7
    cpr
    #
    @8
    csn
    cun
    #
    cfv
    #
    cD
    cA
    @9
    @11
    @6
    @7
    @8
    df-tp
    fveq1i
    @5
    @12
    cA
    @10
    cfv
    #
    cD
    @4
    @12
    @13
    wceq
    #
    @2
    @3
    @4
    cC
    cA
    wne
    @14
    cA
    cC
    necom
    @10
    cC
    cF
    cA
    fvunsn
    sylbi
    ad2antll
    @2
    @3
    @13
    cD
    wceq
    #
    @4
    @0
    @1
    @3
    @15
    cA
    cB
    cD
    cE
    cV
    cW
    fvpr1g
    3expa
    adantrr
    eqtrd
    syl5eq
end
