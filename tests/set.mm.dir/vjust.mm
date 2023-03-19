include "weq.mm"
include "cab.mm"
include "wsb.mm"
include "cv.mm"
include "wcel.mm"
include "equid.mm"
include "sbt.mm"
include "2th.mm"
include "df-clab.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem vjust
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- { x | x = x } = { y | y = y }

  proof
    vz
    vx
    vx
    weq
    #
    vx
    cab
    #
    vy
    vy
    weq
    #
    vy
    cab
    #
    @0
    vx
    vz
    wsb
    #
    @2
    vy
    vz
    wsb
    #
    vz
    cv
    #
    @1
    wcel
    @6
    @3
    wcel
    @4
    @5
    @0
    vx
    vz
    vx
    equid
    sbt
    @2
    vy
    vz
    vy
    equid
    sbt
    2th
    @0
    vz
    vx
    df-clab
    @2
    vz
    vy
    df-clab
    3bitr4i
    eqriv
end
