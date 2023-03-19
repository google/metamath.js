include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "cun.mm"
include "wrel.mm"
include "unss.mm"
include "df-rel.mm"
include "anbi12i.mm"
include "3bitr4ri.mm"

theorem relun
  let cA: class A
  let cB: class B


  assert |- ( Rel ( A u. B ) <-> ( Rel A /\ Rel B ) )

  proof
    cA
    cvv
    cvv
    cxp
    #
    wss
    #
    cB
    @0
    wss
    #
    wa
    cA
    cB
    cun
    #
    @0
    wss
    cA
    wrel
    #
    cB
    wrel
    #
    wa
    @3
    wrel
    cA
    cB
    @0
    unss
    @4
    @1
    @5
    @2
    cA
    df-rel
    cB
    df-rel
    anbi12i
    @3
    df-rel
    3bitr4ri
end
