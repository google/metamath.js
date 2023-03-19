include "cxp.mm"
include "wrel.mm"
include "cvv.mm"
include "wss.mm"
include "xpss.mm"
include "df-rel.mm"
include "mpbir.mm"

theorem relxp
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- Rel ( A X. B )

  proof
    cA
    cB
    cxp
    #
    wrel
    @0
    cvv
    cvv
    cxp
    wss
    cA
    cB
    xpss
    @0
    df-rel
    mpbir
end
