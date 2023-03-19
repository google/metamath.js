include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "xpeq1.mm"
include "id.mm"
include "breq12d.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "breq1d.mm"
include "vex.mm"
include "xpsnen.mm"
include "vtocl2g.mm"

theorem xpsneng
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( A X. { B } ) ~~ A )

  proof
    vx
    cv
    #
    vy
    cv
    #
    csn
    #
    cxp
    #
    @0
    cen
    wbr
    cA
    @2
    cxp
    #
    cA
    cen
    wbr
    cA
    cB
    csn
    #
    cxp
    #
    cA
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
    #
    @3
    @4
    @0
    cA
    cen
    @0
    cA
    @2
    xpeq1
    @7
    id
    breq12d
    @1
    cB
    wceq
    #
    @4
    @6
    cA
    cen
    @8
    @2
    @5
    cA
    @1
    cB
    sneq
    xpeq2d
    breq1d
    @0
    @1
    vx
    vex
    vy
    vex
    xpsnen
    vtocl2g
end
