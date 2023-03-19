include "com.mm"
include "cv.mm"
include "csuc.mm"
include "wlim.mm"
include "wn.mm"
include "con0.mm"
include "crab.mm"
include "wss.mm"
include "dfom2.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem omsson
  let vx: setvar x
  let vy: setvar y


  assert |- _om C_ On

  proof
    com
    vx
    cv
    csuc
    vy
    cv
    wlim
    wn
    vy
    con0
    crab
    wss
    #
    vx
    con0
    crab
    con0
    vx
    vy
    dfom2
    @0
    vx
    con0
    ssrab2
    eqsstri
end
