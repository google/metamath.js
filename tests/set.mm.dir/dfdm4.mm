include "cv.mm"
include "ccnv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "crn.mm"
include "cdm.mm"
include "vex.mm"
include "brcnv.mm"
include "exbii.mm"
include "abbii.mm"
include "dfrn2.mm"
include "df-dm.mm"
include "3eqtr4ri.mm"

theorem dfdm4
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- dom A = ran `' A

  proof
    vy
    cv
    #
    vx
    cv
    #
    cA
    ccnv
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
    cA
    wbr
    #
    vy
    wex
    #
    vx
    cab
    @2
    crn
    cA
    cdm
    @4
    @6
    vx
    @3
    @5
    vy
    @0
    @1
    cA
    vy
    vex
    vx
    vex
    brcnv
    exbii
    abbii
    vy
    vx
    @2
    dfrn2
    vx
    vy
    cA
    df-dm
    3eqtr4ri
end
