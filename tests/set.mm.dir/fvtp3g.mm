include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cop.mm"
include "ctp.mm"
include "cfv.mm"
include "tprot.mm"
include "fveq1i.mm"
include "wceq.mm"
include "wi.mm"
include "necom.mm"
include "fvtp2g.mm"
include "expcom.mm"
include "sylan2b.mm"
include "ancoms.mm"
include "impcom.mm"
include "syl5eq.mm"

theorem fvtp3g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( ( C e. V /\ F e. W ) /\ ( A =/= C /\ B =/= C ) ) -> ( { <. A , D >. , <. B , E >. , <. C , F >. } ` C ) = F )

  proof
    cC
    cV
    wcel
    cF
    cW
    wcel
    wa
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    wa
    #
    wa
    cC
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
    cC
    @5
    @6
    @4
    ctp
    #
    cfv
    #
    cF
    cC
    @7
    @8
    @4
    @5
    @6
    tprot
    fveq1i
    @3
    @0
    @9
    cF
    wceq
    #
    @2
    @1
    @0
    @10
    wi
    #
    @1
    @2
    cC
    cA
    wne
    #
    @11
    cA
    cC
    necom
    @0
    @2
    @12
    wa
    @10
    cB
    cC
    cA
    cE
    cF
    cD
    cV
    cW
    fvtp2g
    expcom
    sylan2b
    ancoms
    impcom
    syl5eq
end
