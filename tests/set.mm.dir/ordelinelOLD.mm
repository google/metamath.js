include "word.mm"
include "w3a.mm"
include "cin.mm"
include "wcel.mm"
include "wo.mm"
include "wceq.mm"
include "wi.mm"
include "ordtri2or3.mm"
include "3adant3.mm"
include "eleq1.mm"
include "orc.mm"
include "syl6bir.mm"
include "olc.mm"
include "jaoi.mm"
include "syl.mm"
include "wss.mm"
include "inss1.mm"
include "wa.mm"
include "ordin.mm"
include "ordtr2.mm"
include "stoic3.mm"
include "mpani.mm"
include "inss2.mm"
include "jaod.mm"
include "impbid.mm"

theorem ordelinelOLD
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
    wi
    #
    @0
    @1
    @11
    @2
    cA
    cB
    ordtri2or3
    3adant3
    @9
    @12
    @10
    @9
    @5
    @6
    @8
    cA
    @4
    cC
    eleq1
    @6
    @7
    orc
    syl6bir
    @10
    @5
    @7
    @8
    cB
    @4
    cC
    eleq1
    @7
    @6
    olc
    syl6bir
    jaoi
    syl
    @3
    @6
    @5
    @7
    @3
    @4
    cA
    wss
    #
    @6
    @5
    cA
    cB
    inss1
    @0
    @1
    @4
    word
    #
    @2
    @13
    @6
    wa
    @5
    wi
    cA
    cB
    ordin
    #
    @4
    cA
    cC
    ordtr2
    stoic3
    mpani
    @3
    @4
    cB
    wss
    #
    @7
    @5
    cA
    cB
    inss2
    @0
    @1
    @14
    @2
    @16
    @7
    wa
    @5
    wi
    @15
    @4
    cB
    cC
    ordtr2
    stoic3
    mpani
    jaod
    impbid
end
