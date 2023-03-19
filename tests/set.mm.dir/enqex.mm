include "ceq.mm"
include "cnpi.mm"
include "cxp.mm"
include "niex.mm"
include "xpex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "cmi.mm"
include "co.mm"
include "wex.mm"
include "copab.mm"
include "df-enq.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "ssexi.mm"

theorem enqex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- ~Q e. _V

  proof
    ceq
    cnpi
    cnpi
    cxp
    #
    @0
    cxp
    #
    @0
    @0
    cnpi
    cnpi
    niex
    niex
    xpex
    #
    @2
    xpex
    ceq
    vx
    cv
    #
    @0
    wcel
    vy
    cv
    #
    @0
    wcel
    wa
    @3
    vz
    cv
    #
    vw
    cv
    #
    cop
    wceq
    @4
    vv
    cv
    #
    vu
    cv
    #
    cop
    wceq
    wa
    @5
    @8
    cmi
    co
    @6
    @7
    cmi
    co
    wceq
    wa
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    #
    wa
    vx
    vy
    copab
    @1
    vx
    vy
    vz
    vw
    vv
    vu
    df-enq
    @9
    vx
    vy
    @0
    @0
    opabssxp
    eqsstri
    ssexi
end
