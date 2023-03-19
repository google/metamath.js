include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "wceq.mm"
include "breq1.mm"
include "rexbidv.mm"
include "cpw.mm"
include "cen.mm"
include "vpwex.mm"
include "numth2.mm"
include "vex.mm"
include "canth2.mm"
include "ensym.mm"
include "sdomentr.mm"
include "sylancr.mm"
include "reximi.mm"
include "ax-mp.mm"
include "vtoclg.mm"

theorem numthcor
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. V -> E. x e. On A ~< x )

  proof
    vy
    cv
    #
    vx
    cv
    #
    csdm
    wbr
    #
    vx
    con0
    wrex
    #
    cA
    @1
    csdm
    wbr
    #
    vx
    con0
    wrex
    vy
    cA
    cV
    @0
    cA
    wceq
    @2
    @4
    vx
    con0
    @0
    cA
    @1
    csdm
    breq1
    rexbidv
    @1
    @0
    cpw
    #
    cen
    wbr
    #
    vx
    con0
    wrex
    @3
    vx
    @5
    vy
    vpwex
    numth2
    @6
    @2
    vx
    con0
    @6
    @0
    @5
    csdm
    wbr
    @5
    @1
    cen
    wbr
    @2
    @0
    vy
    vex
    canth2
    @1
    @5
    ensym
    @0
    @5
    @1
    sdomentr
    sylancr
    reximi
    ax-mp
    vtoclg
end
