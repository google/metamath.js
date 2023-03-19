include "ccoss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "cxrn.mm"
include "crn.mm"
include "df-coss.mm"
include "rnxrn.mm"
include "eqtr4i.mm"

theorem dfcoss4
  let cR: class R
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ,~ R = ran ( R |X. R )

  proof
    cR
    ccoss
    vu
    cv
    #
    vx
    cv
    cR
    wbr
    @0
    vy
    cv
    cR
    wbr
    wa
    vu
    wex
    vx
    vy
    copab
    cR
    cR
    cxrn
    crn
    vx
    vy
    vu
    cR
    df-coss
    vx
    vy
    vu
    cR
    cR
    rnxrn
    eqtr4i
end
