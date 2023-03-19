include "word.mm"
include "wa.mm"
include "wcel.mm"
include "wss.mm"
include "wo.mm"
include "ordtri2or.mm"
include "wi.mm"
include "ordelss.mm"
include "ex.mm"
include "orim1d.mm"
include "adantl.mm"
include "mpd.mm"

theorem ordtri2or2
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A C_ B \/ B C_ A ) )

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
    wcel
    #
    cB
    cA
    wss
    #
    wo
    #
    cA
    cB
    wss
    #
    @3
    wo
    #
    cA
    cB
    ordtri2or
    @1
    @4
    @6
    wi
    @0
    @1
    @2
    @5
    @3
    @1
    @2
    @5
    cB
    cA
    ordelss
    ex
    orim1d
    adantl
    mpd
end
