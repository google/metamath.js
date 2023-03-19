include "wss.mm"
include "cvv.mm"
include "cxp.mm"
include "wrel.mm"
include "sstr2.mm"
include "df-rel.mm"
include "3imtr4g.mm"

theorem relss
  let cA: class A
  let cB: class B


  assert |- ( A C_ B -> ( Rel B -> Rel A ) )

  proof
    cA
    cB
    wss
    cB
    cvv
    cvv
    cxp
    #
    wss
    cA
    @0
    wss
    cB
    wrel
    cA
    wrel
    cA
    cB
    @0
    sstr2
    cB
    df-rel
    cA
    df-rel
    3imtr4g
end
