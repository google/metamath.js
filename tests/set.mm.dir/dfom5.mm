include "com.mm"
include "cv.mm"
include "wlim.mm"
include "cab.mm"
include "cint.mm"
include "wcel.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "elom3.mm"
include "vex.mm"
include "elintab.mm"
include "bitr4i.mm"
include "eqriv.mm"

theorem dfom5
  let vx: setvar x
  let vy: setvar y


  assert |- _om = |^| { x | Lim x }

  proof
    vy
    com
    vx
    cv
    wlim
    #
    vx
    cab
    cint
    #
    vy
    cv
    #
    com
    wcel
    @0
    vy
    vx
    wel
    wi
    vx
    wal
    @2
    @1
    wcel
    vx
    @2
    elom3
    @0
    vx
    @2
    vy
    vex
    elintab
    bitr4i
    eqriv
end
