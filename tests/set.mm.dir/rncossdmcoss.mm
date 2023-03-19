include "cv.mm"
include "ccoss.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "crn.mm"
include "cdm.mm"
include "wb.mm"
include "cvv.mm"
include "brcosscnvcoss.mm"
include "el2v.mm"
include "exbii.mm"
include "abbii.mm"
include "dfrn2.mm"
include "df-dm.mm"
include "3eqtr4i.mm"

theorem rncossdmcoss
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ran ,~ R = dom ,~ R

  proof
    vy
    cv
    #
    vx
    cv
    #
    cR
    ccoss
    #
    wbr
    #
    vy
    wex
    #
    vx
    cab
    @1
    @0
    @2
    wbr
    #
    vy
    wex
    #
    vx
    cab
    @2
    crn
    @2
    cdm
    @4
    @6
    vx
    @3
    @5
    vy
    @3
    @5
    wb
    vy
    vx
    @0
    @1
    cR
    cvv
    cvv
    brcosscnvcoss
    el2v
    exbii
    abbii
    vy
    vx
    @2
    dfrn2
    vx
    vy
    @2
    df-dm
    3eqtr4i
end
