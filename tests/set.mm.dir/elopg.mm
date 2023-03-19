include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "cpr.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "dfopg.mm"
include "eleq2.mm"
include "snex.mm"
include "prex.mm"
include "elpr2.mm"
include "syl6bb.mm"
include "syl.mm"

theorem elopg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( C e. <. A , B >. <-> ( C = { A } \/ C = { A , B } ) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cB
    cop
    #
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    wceq
    #
    cC
    @0
    wcel
    #
    cC
    @1
    wceq
    cC
    @2
    wceq
    wo
    #
    wb
    cA
    cB
    cV
    cW
    dfopg
    @4
    @5
    cC
    @3
    wcel
    @6
    @0
    @3
    cC
    eleq2
    cC
    @1
    @2
    cA
    snex
    cA
    cB
    prex
    elpr2
    syl6bb
    syl
end
