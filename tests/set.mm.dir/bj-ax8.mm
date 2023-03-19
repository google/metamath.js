include "weq.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "equequ2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "cv.mm"
include "df-clel.mm"
include "3bitr4g.mm"
include "biimpd.mm"

theorem bj-ax8
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u


  assert |- ( x = y -> ( x e. z -> y e. z ) )

  proof
    vx
    vy
    weq
    #
    vx
    vz
    wel
    #
    vy
    vz
    wel
    #
    @0
    vu
    vx
    weq
    #
    vu
    vz
    wel
    #
    wa
    #
    vu
    wex
    vu
    vy
    weq
    #
    @4
    wa
    #
    vu
    wex
    @1
    @2
    @0
    @5
    @7
    vu
    @0
    @3
    @6
    @4
    vx
    vy
    vu
    equequ2
    anbi1d
    exbidv
    vu
    vx
    cv
    vz
    cv
    #
    df-clel
    vu
    vy
    cv
    @8
    df-clel
    3bitr4g
    biimpd
end
