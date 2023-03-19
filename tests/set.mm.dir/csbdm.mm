include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "cab.mm"
include "csb.mm"
include "cdm.mm"
include "wsbc.mm"
include "csbab.mm"
include "sbcex2.mm"
include "sbcel2.mm"
include "exbii.mm"
include "bitri.mm"
include "abbii.mm"
include "eqtri.mm"
include "dfdm3.mm"
include "csbeq2i.mm"
include "3eqtr4i.mm"

theorem csbdm
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vy: setvar y


  assert |- [_ A / x ]_ dom B = dom [_ A / x ]_ B

  proof
    vx
    cA
    vy
    cv
    vw
    cv
    cop
    #
    cB
    wcel
    #
    vw
    wex
    #
    vy
    cab
    #
    csb
    #
    @0
    vx
    cA
    cB
    csb
    #
    wcel
    #
    vw
    wex
    #
    vy
    cab
    #
    vx
    cA
    cB
    cdm
    #
    csb
    @5
    cdm
    @4
    @2
    vx
    cA
    wsbc
    #
    vy
    cab
    @8
    @2
    vx
    vy
    cA
    csbab
    @10
    @7
    vy
    @10
    @1
    vx
    cA
    wsbc
    #
    vw
    wex
    @7
    @1
    vw
    vx
    cA
    sbcex2
    @11
    @6
    vw
    vx
    cA
    @0
    cB
    sbcel2
    exbii
    bitri
    abbii
    eqtri
    vx
    cA
    @9
    @3
    vy
    vw
    cB
    dfdm3
    csbeq2i
    vy
    vw
    @5
    dfdm3
    3eqtr4i
end
