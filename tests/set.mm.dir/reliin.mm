include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrex.mm"
include "ciin.mm"
include "wrel.mm"
include "iinss.mm"
include "df-rel.mm"
include "rexbii.mm"
include "3imtr4i.mm"

theorem reliin
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( E. x e. A Rel B -> Rel |^|_ x e. A B )

  proof
    cB
    cvv
    cvv
    cxp
    #
    wss
    #
    vx
    cA
    wrex
    vx
    cA
    cB
    ciin
    #
    @0
    wss
    cB
    wrel
    #
    vx
    cA
    wrex
    @2
    wrel
    vx
    cA
    cB
    @0
    iinss
    @3
    @1
    vx
    cA
    cB
    df-rel
    rexbii
    @2
    df-rel
    3imtr4i
end
