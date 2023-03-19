include "ccom.mm"
include "wss.mm"
include "wceq.mm"
include "id.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "cleq2lem.mm"

theorem trcleq2lemRP
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> ( ( R C_ A /\ ( A o. A ) C_ A ) <-> ( R C_ B /\ ( B o. B ) C_ B ) ) )

  proof
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
    cA
    cB
    wceq
    #
    @0
    @1
    cA
    cB
    @2
    cA
    cB
    cA
    cB
    @2
    id
    #
    @3
    coeq12d
    @3
    sseq12d
    cleq2lem
end
