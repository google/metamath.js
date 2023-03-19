include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cima.mm"
include "crn.mm"
include "vex.mm"
include "opeldm.mm"
include "pm4.71i.mm"
include "ancom.mm"
include "bitr2i.mm"
include "exbii.mm"
include "abbii.mm"
include "dfima3.mm"
include "dfrn3.mm"
include "3eqtr4i.mm"

theorem imadmrn
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A " dom A ) = ran A

  proof
    vx
    cv
    #
    cA
    cdm
    #
    wcel
    #
    @0
    vy
    cv
    #
    cop
    cA
    wcel
    #
    wa
    #
    vx
    wex
    #
    vy
    cab
    @4
    vx
    wex
    #
    vy
    cab
    cA
    @1
    cima
    cA
    crn
    @6
    @7
    vy
    @5
    @4
    vx
    @4
    @4
    @2
    wa
    @5
    @4
    @2
    @0
    @3
    cA
    vx
    vex
    vy
    vex
    opeldm
    pm4.71i
    @4
    @2
    ancom
    bitr2i
    exbii
    abbii
    vx
    vy
    cA
    @1
    dfima3
    vx
    vy
    cA
    dfrn3
    3eqtr4i
end
