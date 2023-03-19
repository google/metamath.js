include "crpss.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cun.mm"
include "simprr.mm"
include "wceq.mm"
include "wb.mm"
include "ssequn1.mm"
include "eleq1.mm"
include "sylbi.mm"
include "syl5ibrcom.mm"
include "simprl.mm"
include "ssequn2.mm"
include "sorpssi.mm"
include "mpjaod.mm"

theorem sorpssun
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( [C.] Or A /\ ( B e. A /\ C e. A ) ) -> ( B u. C ) e. A )

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
    cun
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
    @2
    @0
    @1
    @2
    simprr
    @4
    @5
    cC
    wceq
    @6
    @2
    wb
    cB
    cC
    ssequn1
    @5
    cC
    cA
    eleq1
    sylbi
    syl5ibrcom
    @3
    @6
    @7
    @1
    @0
    @1
    @2
    simprl
    @7
    @5
    cB
    wceq
    @6
    @1
    wb
    cC
    cB
    ssequn2
    @5
    cB
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
