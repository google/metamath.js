include "word.mm"
include "wa.mm"
include "wcel.mm"
include "wss.mm"
include "wn.mm"
include "wb.mm"
include "ordtri1.mm"
include "ancoms.mm"
include "biimprd.mm"
include "orrd.mm"

theorem ordtri2or
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A e. B \/ B C_ A ) )

  proof
    cA
    word
    #
    cB
    word
    #
    wa
    #
    cA
    cB
    wcel
    #
    cB
    cA
    wss
    #
    @2
    @4
    @3
    wn
    #
    @1
    @0
    @4
    @5
    wb
    cB
    cA
    ordtri1
    ancoms
    biimprd
    orrd
end
