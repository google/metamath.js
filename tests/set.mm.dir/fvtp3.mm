include "wne.mm"
include "wa.mm"
include "cop.mm"
include "ctp.mm"
include "cfv.mm"
include "tprot.mm"
include "fveq1i.mm"
include "wceq.mm"
include "necom.mm"
include "fvtp2.mm"
include "sylan2b.mm"
include "ancoms.mm"
include "syl5eq.mm"

theorem fvtp3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume fvtp3.1: |- C e. _V
  assume fvtp3.4: |- F e. _V


  assert |- ( ( A =/= C /\ B =/= C ) -> ( { <. A , D >. , <. B , E >. , <. C , F >. } ` C ) = F )

  proof
    cA
    cC
    wne
    #
    cB
    cC
    wne
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
    @3
    @4
    @2
    ctp
    #
    cfv
    #
    cF
    cC
    @5
    @6
    @2
    @3
    @4
    tprot
    fveq1i
    @1
    @0
    @7
    cF
    wceq
    #
    @0
    @1
    cC
    cA
    wne
    @8
    cA
    cC
    necom
    cB
    cC
    cA
    cE
    cF
    cD
    fvtp3.1
    fvtp3.4
    fvtp2
    sylan2b
    ancoms
    syl5eq
end
