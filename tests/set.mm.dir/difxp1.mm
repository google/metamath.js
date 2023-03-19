include "cxp.mm"
include "cdif.mm"
include "cun.mm"
include "c0.mm"
include "difxp.mm"
include "difid.mm"
include "xpeq2i.mm"
include "xp0.mm"
include "eqtri.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtrri.mm"

theorem difxp1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A \ B ) X. C ) = ( ( A X. C ) \ ( B X. C ) )

  proof
    cA
    cC
    cxp
    cB
    cC
    cxp
    cdif
    cA
    cB
    cdif
    cC
    cxp
    #
    cA
    cC
    cC
    cdif
    #
    cxp
    #
    cun
    @0
    c0
    cun
    @0
    cB
    cC
    cA
    cC
    difxp
    @2
    c0
    @0
    @2
    cA
    c0
    cxp
    c0
    @1
    c0
    cA
    cC
    difid
    xpeq2i
    cA
    xp0
    eqtri
    uneq2i
    @0
    un0
    3eqtrri
end
