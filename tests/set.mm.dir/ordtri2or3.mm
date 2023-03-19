include "word.mm"
include "wa.mm"
include "wss.mm"
include "wo.mm"
include "cin.mm"
include "wceq.mm"
include "ordtri2or2.mm"
include "dfss.mm"
include "sseqin2.mm"
include "eqcom.mm"
include "bitri.mm"
include "orbi12i.mm"
include "sylib.mm"

theorem ordtri2or3
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A = ( A i^i B ) \/ B = ( A i^i B ) ) )

  proof
    cA
    word
    cB
    word
    wa
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wo
    cA
    cA
    cB
    cin
    #
    wceq
    #
    cB
    @2
    wceq
    #
    wo
    cA
    cB
    ordtri2or2
    @0
    @3
    @1
    @4
    cA
    cB
    dfss
    @1
    @2
    cB
    wceq
    @4
    cB
    cA
    sseqin2
    @2
    cB
    eqcom
    bitri
    orbi12i
    sylib
end
