include "word.mm"
include "wa.mm"
include "wss.mm"
include "wo.mm"
include "cun.mm"
include "wceq.mm"
include "ordtri2or2.mm"
include "orcomd.mm"
include "eqeq1.mm"
include "ssequn2.mm"
include "syl6rbbr.mm"
include "ssequn1.mm"
include "orbi12d.mm"
include "syl5ibcom.mm"

theorem ordequn
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Ord B /\ Ord C ) -> ( A = ( B u. C ) -> ( A = B \/ A = C ) ) )

  proof
    cB
    word
    cC
    word
    wa
    #
    cC
    cB
    wss
    #
    cB
    cC
    wss
    #
    wo
    cA
    cB
    cC
    cun
    #
    wceq
    #
    cA
    cB
    wceq
    #
    cA
    cC
    wceq
    #
    wo
    @0
    @2
    @1
    cB
    cC
    ordtri2or2
    orcomd
    @4
    @1
    @5
    @2
    @6
    @4
    @5
    @3
    cB
    wceq
    @1
    cA
    @3
    cB
    eqeq1
    cC
    cB
    ssequn2
    syl6rbbr
    @4
    @6
    @3
    cC
    wceq
    @2
    cA
    @3
    cC
    eqeq1
    cB
    cC
    ssequn1
    syl6rbbr
    orbi12d
    syl5ibcom
end
