include "crn.mm"
include "ccnv.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "df-rn.mm"
include "df-dm.mm"
include "vex.mm"
include "brcnv.mm"
include "exbii.mm"
include "abbii.mm"
include "3eqtri.mm"

theorem dfrn2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ran A = { y | E. x x A y }

  proof
    cA
    crn
    cA
    ccnv
    #
    cdm
    vy
    cv
    #
    vx
    cv
    #
    @0
    wbr
    #
    vx
    wex
    #
    vy
    cab
    @2
    @1
    cA
    wbr
    #
    vx
    wex
    #
    vy
    cab
    cA
    df-rn
    vy
    vx
    @0
    df-dm
    @4
    @6
    vy
    @3
    @5
    vx
    @1
    @2
    cA
    vy
    vex
    vx
    vex
    brcnv
    exbii
    abbii
    3eqtri
end
