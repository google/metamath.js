include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "word.mm"
include "wcel.mm"
include "wn.mm"
include "eqss.mm"
include "wb.mm"
include "ordtri1.mm"
include "ancoms.mm"
include "anbi2d.mm"
include "syl5bb.mm"

theorem ordtri4
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A = B <-> ( A C_ B /\ -. A e. B ) ) )

  proof
    cA
    cB
    wceq
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    cA
    word
    #
    cB
    word
    #
    wa
    #
    @0
    cA
    cB
    wcel
    wn
    #
    wa
    cA
    cB
    eqss
    @4
    @1
    @5
    @0
    @3
    @2
    @1
    @5
    wb
    cB
    cA
    ordtri1
    ancoms
    anbi2d
    syl5bb
end
