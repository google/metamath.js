include "word.mm"
include "wcel.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "wtr.mm"
include "ordtr.mm"
include "tz7.7.mm"
include "sylan2.mm"
include "ancoms.mm"

theorem ordelssne
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> ( A C_ B /\ A =/= B ) ) )

  proof
    cB
    word
    #
    cA
    word
    #
    cA
    cB
    wcel
    cA
    cB
    wss
    cA
    cB
    wne
    wa
    wb
    #
    @1
    @0
    cA
    wtr
    @2
    cA
    ordtr
    cB
    cA
    tz7.7
    sylan2
    ancoms
end
