include "cltp.mm"
include "cv.mm"
include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "wpss.mm"
include "copab.mm"
include "cxp.mm"
include "df-ltp.mm"
include "opabssxp.mm"
include "eqsstri.mm"

theorem ltrelpr
  let vx: setvar x
  let vy: setvar y


  assert |- <P C_ ( P. X. P. )

  proof
    cltp
    vx
    cv
    #
    cnp
    wcel
    vy
    cv
    #
    cnp
    wcel
    wa
    @0
    @1
    wpss
    #
    wa
    vx
    vy
    copab
    cnp
    cnp
    cxp
    vx
    vy
    df-ltp
    @2
    vx
    vy
    cnp
    cnp
    opabssxp
    eqsstri
end
