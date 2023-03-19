include "cxp.mm"
include "wrel.mm"
include "cin.mm"
include "relxp.mm"
include "relin2.mm"
include "ax-mp.mm"

theorem relinxp
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- Rel ( R i^i ( A X. B ) )

  proof
    cA
    cB
    cxp
    #
    wrel
    cR
    @0
    cin
    wrel
    cA
    cB
    relxp
    cR
    @0
    relin2
    ax-mp
end
