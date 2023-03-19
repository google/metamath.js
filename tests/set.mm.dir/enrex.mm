include "cer.mm"
include "cnp.mm"
include "cxp.mm"
include "npex.mm"
include "xpex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "cpp.mm"
include "co.mm"
include "wex.mm"
include "copab.mm"
include "df-enr.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "ssexi.mm"

theorem enrex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- ~R e. _V

  proof
    cer
    cnp
    cnp
    cxp
    #
    @0
    cxp
    #
    @0
    @0
    cnp
    cnp
    npex
    npex
    xpex
    #
    @2
    xpex
    cer
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
    cpp
    co
    @6
    @7
    cpp
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
    df-enr
    @9
    vx
    vy
    @0
    @0
    opabssxp
    eqsstri
    ssexi
end
