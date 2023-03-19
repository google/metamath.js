include "ctop.mm"
include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "cuni.mm"
include "cun.mm"
include "wceq.mm"
include "uniprg.mm"
include "3adant1.mm"
include "wa.mm"
include "wss.mm"
include "prssi.mm"
include "uniopn.mm"
include "sylan2.mm"
include "3impb.mm"
include "eqeltrrd.mm"

theorem unopn
  let cA: class A
  let cB: class B
  let cJ: class J


  assert |- ( ( J e. Top /\ A e. J /\ B e. J ) -> ( A u. B ) e. J )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cJ
    wcel
    #
    cB
    cJ
    wcel
    #
    w3a
    cA
    cB
    cpr
    #
    cuni
    #
    cA
    cB
    cun
    #
    cJ
    @1
    @2
    @4
    @5
    wceq
    @0
    cA
    cB
    cJ
    cJ
    uniprg
    3adant1
    @0
    @1
    @2
    @4
    cJ
    wcel
    #
    @1
    @2
    wa
    @0
    @3
    cJ
    wss
    @6
    cA
    cB
    cJ
    prssi
    @3
    cJ
    uniopn
    sylan2
    3impb
    eqeltrrd
end
