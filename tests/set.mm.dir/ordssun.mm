include "word.mm"
include "wa.mm"
include "cun.mm"
include "wss.mm"
include "wo.mm"
include "wi.mm"
include "ordtri2or2.mm"
include "wceq.mm"
include "wb.mm"
include "ssequn1.mm"
include "sseq2.mm"
include "sylbi.mm"
include "olc.mm"
include "syl6bi.mm"
include "ssequn2.mm"
include "orc.mm"
include "jaoi.mm"
include "syl.mm"
include "ssun.mm"
include "impbid1.mm"

theorem ordssun
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Ord B /\ Ord C ) -> ( A C_ ( B u. C ) <-> ( A C_ B \/ A C_ C ) ) )

  proof
    cB
    word
    cC
    word
    wa
    #
    cA
    cB
    cC
    cun
    #
    wss
    #
    cA
    cB
    wss
    #
    cA
    cC
    wss
    #
    wo
    #
    @0
    cB
    cC
    wss
    #
    cC
    cB
    wss
    #
    wo
    @2
    @5
    wi
    #
    cB
    cC
    ordtri2or2
    @6
    @8
    @7
    @6
    @2
    @4
    @5
    @6
    @1
    cC
    wceq
    @2
    @4
    wb
    cB
    cC
    ssequn1
    @1
    cC
    cA
    sseq2
    sylbi
    @4
    @3
    olc
    syl6bi
    @7
    @2
    @3
    @5
    @7
    @1
    cB
    wceq
    @2
    @3
    wb
    cC
    cB
    ssequn2
    @1
    cB
    cA
    sseq2
    sylbi
    @3
    @4
    orc
    syl6bi
    jaoi
    syl
    cA
    cB
    cC
    ssun
    impbid1
end
