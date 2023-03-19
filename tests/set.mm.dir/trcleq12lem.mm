include "wceq.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cleq1lem.mm"
include "trcleq2lem.mm"
include "sylan9bb.mm"

theorem trcleq12lem
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S


  assert |- ( ( R = S /\ A = B ) -> ( ( R C_ A /\ ( A o. A ) C_ A ) <-> ( S C_ B /\ ( B o. B ) C_ B ) ) )

  proof
    cR
    cS
    wceq
    cR
    cA
    wss
    cA
    cA
    ccom
    cA
    wss
    #
    wa
    cS
    cA
    wss
    @0
    wa
    cA
    cB
    wceq
    cS
    cB
    wss
    cB
    cB
    ccom
    cB
    wss
    wa
    @0
    cR
    cS
    cA
    cleq1lem
    cA
    cB
    cS
    trcleq2lem
    sylan9bb
end
