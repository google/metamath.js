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
include "fvtp1g.mm"
include "expcom.mm"
include "ancoms.mm"
include "sylanb.mm"
include "impcom.mm"
include "syl5eq.mm"

theorem fvtp2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( ( B e. V /\ E e. W ) /\ ( A =/= B /\ B =/= C ) ) -> ( { <. A , D >. , <. B , E >. , <. C , F >. } ` B ) = E )

  proof
    cB
    cV
    wcel
    cE
    cW
    wcel
    wa
    #
    cA
    cB
    wne
    #
    cB
    cC
    wne
    #
    wa
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
    @5
    @6
    @4
    ctp
    #
    cfv
    #
    cE
    cB
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
    cE
    wceq
    #
    @1
    cB
    cA
    wne
    #
    @2
    @0
    @10
    wi
    #
    cA
    cB
    necom
    @2
    @11
    @12
    @0
    @2
    @11
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
    fvtp1g
    expcom
    ancoms
    sylanb
    impcom
    syl5eq
end
