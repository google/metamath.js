include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "cun.mm"
include "cdm.mm"
include "wo.mm"
include "unab.mm"
include "brun.mm"
include "exbii.mm"
include "19.43.mm"
include "bitr2i.mm"
include "abbii.mm"
include "eqtri.mm"
include "df-dm.mm"
include "uneq12i.mm"
include "3eqtr4ri.mm"

theorem dmun
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cR: class R


  assert |- dom ( A u. B ) = ( dom A u. dom B )

  proof
    vy
    cv
    #
    vx
    cv
    #
    cA
    wbr
    #
    vx
    wex
    #
    vy
    cab
    #
    @0
    @1
    cB
    wbr
    #
    vx
    wex
    #
    vy
    cab
    #
    cun
    #
    @0
    @1
    cA
    cB
    cun
    #
    wbr
    #
    vx
    wex
    #
    vy
    cab
    #
    cA
    cdm
    #
    cB
    cdm
    #
    cun
    @9
    cdm
    @8
    @3
    @6
    wo
    #
    vy
    cab
    @12
    @3
    @6
    vy
    unab
    @15
    @11
    vy
    @11
    @2
    @5
    wo
    #
    vx
    wex
    @15
    @10
    @16
    vx
    @0
    @1
    cA
    cB
    brun
    exbii
    @2
    @5
    vx
    19.43
    bitr2i
    abbii
    eqtri
    @13
    @4
    @14
    @7
    vy
    vx
    cA
    df-dm
    vy
    vx
    cB
    df-dm
    uneq12i
    vy
    vx
    @9
    df-dm
    3eqtr4ri
end
