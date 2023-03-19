include "word.mm"
include "wa.mm"
include "wceq.mm"
include "wcel.mm"
include "wo.mm"
include "wn.mm"
include "wb.mm"
include "wss.mm"
include "ordsseleq.mm"
include "eqcom.mm"
include "orbi2i.mm"
include "orcom.mm"
include "bitri.mm"
include "syl6bb.mm"
include "ordtri1.mm"
include "bitr3d.mm"
include "ancoms.mm"
include "con2bid.mm"

theorem ordtri2
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> -. ( A = B \/ B e. A ) ) )

  proof
    cA
    word
    #
    cB
    word
    #
    wa
    cA
    cB
    wceq
    #
    cB
    cA
    wcel
    #
    wo
    #
    cA
    cB
    wcel
    #
    @1
    @0
    @4
    @5
    wn
    #
    wb
    @1
    @0
    wa
    #
    cB
    cA
    wss
    #
    @4
    @6
    @7
    @8
    @3
    cB
    cA
    wceq
    #
    wo
    #
    @4
    cB
    cA
    ordsseleq
    @10
    @3
    @2
    wo
    @4
    @9
    @2
    @3
    cB
    cA
    eqcom
    orbi2i
    @3
    @2
    orcom
    bitri
    syl6bb
    cB
    cA
    ordtri1
    bitr3d
    ancoms
    con2bid
end
