include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "divne0b.mm"
include "3expb.mm"
include "biimpa.mm"
include "an32s.mm"

theorem divne0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( A / B ) =/= 0 )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    cA
    cc0
    wne
    #
    cA
    cB
    cdiv
    co
    cc0
    wne
    #
    @0
    @3
    wa
    @4
    @5
    @0
    @1
    @2
    @4
    @5
    wb
    cA
    cB
    divne0b
    3expb
    biimpa
    an32s
end
