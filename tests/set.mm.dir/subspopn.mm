include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "wi.mm"
include "w3a.mm"
include "cin.mm"
include "elrestr.mm"
include "wceq.mm"
include "wb.mm"
include "df-ss.mm"
include "eleq1.mm"
include "sylbi.mm"
include "syl5ibcom.mm"
include "3expa.mm"
include "impr.mm"

theorem subspopn
  let cA: class A
  let cB: class B
  let cJ: class J
  let cV: class V


  assert |- ( ( ( J e. Top /\ A e. V ) /\ ( B e. J /\ B C_ A ) ) -> B e. ( J |`t A ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    cB
    cJ
    wcel
    #
    cB
    cA
    wss
    #
    cB
    cJ
    cA
    crest
    co
    #
    wcel
    #
    @0
    @1
    @2
    @3
    @5
    wi
    @0
    @1
    @2
    w3a
    cB
    cA
    cin
    #
    @4
    wcel
    #
    @3
    @5
    cB
    cA
    cJ
    ctop
    cV
    elrestr
    @3
    @6
    cB
    wceq
    @7
    @5
    wb
    cB
    cA
    df-ss
    @6
    cB
    @4
    eleq1
    sylbi
    syl5ibcom
    3expa
    impr
end
