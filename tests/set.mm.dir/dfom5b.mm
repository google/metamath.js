include "com.mm"
include "con0.mm"
include "climits.mm"
include "cint.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wlim.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "vex.mm"
include "elint.mm"
include "ellimits.mm"
include "imbi1i.mm"
include "albii.mm"
include "bitr2i.mm"
include "anbi2i.mm"
include "elom.mm"
include "elin.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem dfom5b
  let vx: setvar x
  let vy: setvar y


  assert |- _om = ( On i^i |^| Limits )

  proof
    vx
    com
    con0
    climits
    cint
    #
    cin
    #
    vx
    cv
    #
    con0
    wcel
    #
    vy
    cv
    #
    wlim
    #
    @2
    @4
    wcel
    #
    wi
    #
    vy
    wal
    #
    wa
    @3
    @2
    @0
    wcel
    #
    wa
    @2
    com
    wcel
    @2
    @1
    wcel
    @8
    @9
    @3
    @9
    @4
    climits
    wcel
    #
    @6
    wi
    #
    vy
    wal
    @8
    vy
    @2
    climits
    vx
    vex
    elint
    @11
    @7
    vy
    @10
    @5
    @6
    @4
    vy
    vex
    ellimits
    imbi1i
    albii
    bitr2i
    anbi2i
    vy
    @2
    elom
    @2
    con0
    @0
    elin
    3bitr4i
    eqriv
end
