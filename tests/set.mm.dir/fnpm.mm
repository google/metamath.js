include "cvv.mm"
include "cv.mm"
include "wfun.mm"
include "cxp.mm"
include "cpw.mm"
include "crab.mm"
include "cpm.mm"
include "df-pm.mm"
include "vex.mm"
include "xpex.mm"
include "pwex.mm"
include "rabex.mm"
include "fnmpt2i.mm"

theorem fnpm
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ^pm Fn ( _V X. _V )

  proof
    vx
    vy
    cvv
    cvv
    vf
    cv
    wfun
    #
    vf
    vy
    cv
    #
    vx
    cv
    #
    cxp
    #
    cpw
    #
    crab
    cpm
    vx
    vy
    vf
    df-pm
    @0
    vf
    @4
    @3
    @1
    @2
    vy
    vex
    vx
    vex
    xpex
    pwex
    rabex
    fnmpt2i
end
