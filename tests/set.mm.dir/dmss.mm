include "wss.mm"
include "cdm.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "ssel.mm"
include "eximdv.mm"
include "vex.mm"
include "eldm2.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem dmss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A C_ B -> dom A C_ dom B )

  proof
    cA
    cB
    wss
    #
    vx
    cA
    cdm
    #
    cB
    cdm
    #
    @0
    vx
    cv
    #
    vy
    cv
    cop
    #
    cA
    wcel
    #
    vy
    wex
    @4
    cB
    wcel
    #
    vy
    wex
    @3
    @1
    wcel
    @3
    @2
    wcel
    @0
    @5
    @6
    vy
    cA
    cB
    @4
    ssel
    eximdv
    vy
    @3
    cA
    vx
    vex
    #
    eldm2
    vy
    @3
    cB
    @7
    eldm2
    3imtr4g
    ssrdv
end
