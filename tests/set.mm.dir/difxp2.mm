include "cxp.mm"
include "cdif.mm"
include "cun.mm"
include "c0.mm"
include "difxp.mm"
include "difid.mm"
include "xpeq1i.mm"
include "0xp.mm"
include "eqtri.mm"
include "uneq1i.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtrri.mm"

theorem difxp2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A X. ( B \ C ) ) = ( ( A X. B ) \ ( A X. C ) )

  proof
    cA
    cB
    cxp
    cA
    cC
    cxp
    cdif
    cA
    cA
    cdif
    #
    cB
    cxp
    #
    cA
    cB
    cC
    cdif
    cxp
    #
    cun
    c0
    @2
    cun
    #
    @2
    cA
    cC
    cA
    cB
    difxp
    @1
    c0
    @2
    @1
    c0
    cB
    cxp
    c0
    @0
    c0
    cB
    cA
    difid
    xpeq1i
    cB
    0xp
    eqtri
    uneq1i
    @3
    @2
    c0
    cun
    @2
    c0
    @2
    uncom
    @2
    un0
    eqtri
    3eqtrri
end
