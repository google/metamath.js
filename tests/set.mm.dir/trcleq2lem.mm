include "wceq.mm"
include "wss.mm"
include "ccom.mm"
include "sseq2.mm"
include "id.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "anbi12d.mm"

theorem trcleq2lem
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> ( ( R C_ A /\ ( A o. A ) C_ A ) <-> ( R C_ B /\ ( B o. B ) C_ B ) ) )

  proof
    cA
    cB
    wceq
    #
    cR
    cA
    wss
    cR
    cB
    wss
    cA
    cA
    ccom
    #
    cA
    wss
    cB
    cB
    ccom
    #
    cB
    wss
    cA
    cB
    cR
    sseq2
    @0
    @1
    @2
    cA
    cB
    @0
    cA
    cB
    cA
    cB
    @0
    id
    #
    @3
    coeq12d
    @3
    sseq12d
    anbi12d
end
