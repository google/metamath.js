include "word.mm"
include "wa.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wpss.mm"
include "wss.mm"
include "ordelpss.mm"
include "orbi1d.mm"
include "sspss.mm"
include "syl6rbbr.mm"

theorem ordsseleq
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> ( A e. B \/ A = B ) ) )

  proof
    cA
    word
    cB
    word
    wa
    #
    cA
    cB
    wcel
    #
    cA
    cB
    wceq
    #
    wo
    cA
    cB
    wpss
    #
    @2
    wo
    cA
    cB
    wss
    @0
    @1
    @3
    @2
    cA
    cB
    ordelpss
    orbi1d
    cA
    cB
    sspss
    syl6rbbr
end
