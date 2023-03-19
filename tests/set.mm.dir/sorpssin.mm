include "crpss.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cin.mm"
include "simprl.mm"
include "wceq.mm"
include "wb.mm"
include "df-ss.mm"
include "eleq1.mm"
include "sylbi.mm"
include "syl5ibrcom.mm"
include "simprr.mm"
include "sseqin2.mm"
include "sorpssi.mm"
include "mpjaod.mm"

theorem sorpssin
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( [C.] Or A /\ ( B e. A /\ C e. A ) ) -> ( B i^i C ) e. A )

  proof
    cA
    crpss
    wor
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    wa
    wa
    #
    cB
    cC
    wss
    #
    cB
    cC
    cin
    #
    cA
    wcel
    #
    cC
    cB
    wss
    #
    @3
    @6
    @4
    @1
    @0
    @1
    @2
    simprl
    @4
    @5
    cB
    wceq
    @6
    @1
    wb
    cB
    cC
    df-ss
    @5
    cB
    cA
    eleq1
    sylbi
    syl5ibrcom
    @3
    @6
    @7
    @2
    @0
    @1
    @2
    simprr
    @7
    @5
    cC
    wceq
    @6
    @2
    wb
    cC
    cB
    sseqin2
    @5
    cC
    cA
    eleq1
    sylbi
    syl5ibrcom
    cA
    cB
    cC
    sorpssi
    mpjaod
end
