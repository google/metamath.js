include "cltr.mm"
include "cv.mm"
include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "wceq.mm"
include "cpp.mm"
include "co.mm"
include "cltp.mm"
include "wbr.mm"
include "wex.mm"
include "copab.mm"
include "cxp.mm"
include "df-ltr.mm"
include "opabssxp.mm"
include "eqsstri.mm"

theorem ltrelsr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- <R C_ ( R. X. R. )

  proof
    cltr
    vx
    cv
    #
    cnr
    wcel
    vy
    cv
    #
    cnr
    wcel
    wa
    @0
    vz
    cv
    #
    vw
    cv
    #
    cop
    cer
    cec
    wceq
    @1
    vv
    cv
    #
    vu
    cv
    #
    cop
    cer
    cec
    wceq
    wa
    @2
    @5
    cpp
    co
    @3
    @4
    cpp
    co
    cltp
    wbr
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
    cnr
    cnr
    cxp
    vx
    vy
    vz
    vw
    vv
    vu
    df-ltr
    @6
    vx
    vy
    cnr
    cnr
    opabssxp
    eqsstri
end
