include "wceq.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "sseq1.mm"
include "df-rel.mm"
include "3bitr4g.mm"

theorem releq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( Rel A <-> Rel B ) )

  proof
    cA
    cB
    wceq
    cA
    cvv
    cvv
    cxp
    #
    wss
    cB
    @0
    wss
    cA
    wrel
    cB
    wrel
    cA
    cB
    @0
    sseq1
    cA
    df-rel
    cB
    df-rel
    3bitr4g
end
