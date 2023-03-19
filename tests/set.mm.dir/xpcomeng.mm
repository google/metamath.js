include "cv.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "xpeq1.mm"
include "xpeq2.mm"
include "breq12d.mm"
include "vex.mm"
include "xpcomen.mm"
include "vtocl2g.mm"

theorem xpcomeng
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( A X. B ) ~~ ( B X. A ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    @1
    @0
    cxp
    #
    cen
    wbr
    cA
    @1
    cxp
    #
    @1
    cA
    cxp
    #
    cen
    wbr
    cA
    cB
    cxp
    #
    cB
    cA
    cxp
    #
    cen
    wbr
    vx
    vy
    cA
    cB
    cV
    cW
    @0
    cA
    wceq
    @2
    @4
    @3
    @5
    cen
    @0
    cA
    @1
    xpeq1
    @0
    cA
    @1
    xpeq2
    breq12d
    @1
    cB
    wceq
    @4
    @6
    @5
    @7
    cen
    @1
    cB
    cA
    xpeq2
    @1
    cB
    cA
    xpeq1
    breq12d
    @0
    @1
    vx
    vex
    vy
    vex
    xpcomen
    vtocl2g
end
