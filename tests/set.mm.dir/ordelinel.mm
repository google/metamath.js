include "word.mm"
include "w3a.mm"
include "cin.mm"
include "wcel.mm"
include "wo.mm"
include "wceq.mm"
include "ordtri2or3.mm"
include "3adant3.mm"
include "eleq1a.mm"
include "orim12d.mm"
include "syl5com.mm"
include "wi.mm"
include "ordin.mm"
include "wa.mm"
include "wss.mm"
include "inss1.mm"
include "ordtr2.mm"
include "mpani.mm"
include "inss2.mm"
include "jaod.mm"
include "stoic3.mm"
include "impbid.mm"

theorem ordelinel
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Ord A /\ Ord B /\ Ord C ) -> ( ( A i^i B ) e. C <-> ( A e. C \/ B e. C ) ) )

  proof
    cA
    word
    #
    cB
    word
    #
    cC
    word
    #
    w3a
    #
    cA
    cB
    cin
    #
    cC
    wcel
    #
    cA
    cC
    wcel
    #
    cB
    cC
    wcel
    #
    wo
    #
    @3
    cA
    @4
    wceq
    #
    cB
    @4
    wceq
    #
    wo
    #
    @5
    @8
    @0
    @1
    @11
    @2
    cA
    cB
    ordtri2or3
    3adant3
    @5
    @9
    @6
    @10
    @7
    @4
    cC
    cA
    eleq1a
    @4
    cC
    cB
    eleq1a
    orim12d
    syl5com
    @0
    @1
    @4
    word
    #
    @2
    @8
    @5
    wi
    cA
    cB
    ordin
    @12
    @2
    wa
    #
    @6
    @5
    @7
    @13
    @4
    cA
    wss
    @6
    @5
    cA
    cB
    inss1
    @4
    cA
    cC
    ordtr2
    mpani
    @13
    @4
    cB
    wss
    @7
    @5
    cA
    cB
    inss2
    @4
    cB
    cC
    ordtr2
    mpani
    jaod
    stoic3
    impbid
end
