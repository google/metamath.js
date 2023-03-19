include "wne.mm"
include "wa.mm"
include "cop.mm"
include "ctp.mm"
include "cfv.mm"
include "tprot.mm"
include "fveq1i.mm"
include "wceq.mm"
include "necom.mm"
include "fvtp1.mm"
include "ancoms.mm"
include "sylanb.mm"
include "syl5eq.mm"

theorem fvtp2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume fvtp2.1: |- B e. _V
  assume fvtp2.4: |- E e. _V


  assert |- ( ( A =/= B /\ B =/= C ) -> ( { <. A , D >. , <. B , E >. , <. C , F >. } ` B ) = E )

  proof
    cA
    cB
    wne
    #
    cB
    cC
    wne
    #
    wa
    cB
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
    cB
    @3
    @4
    @2
    ctp
    #
    cfv
    #
    cE
    cB
    @5
    @6
    @2
    @3
    @4
    tprot
    fveq1i
    @0
    cB
    cA
    wne
    #
    @1
    @7
    cE
    wceq
    #
    cA
    cB
    necom
    @1
    @8
    @9
    cB
    cC
    cA
    cE
    cF
    cD
    fvtp2.1
    fvtp2.4
    fvtp1
    ancoms
    sylanb
    syl5eq
end
