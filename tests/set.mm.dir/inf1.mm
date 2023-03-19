include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "anim1i.mm"
include "eximii.mm"

theorem inf1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume inf1.1: |- E. x ( y e. x /\ A. y ( y e. x -> E. z ( y e. z /\ z e. x ) ) )


  assert |- E. x ( x =/= (/) /\ A. y ( y e. x -> E. z ( y e. z /\ z e. x ) ) )

  proof
    vy
    vx
    wel
    #
    @0
    vy
    vz
    wel
    vz
    vx
    wel
    wa
    vz
    wex
    wi
    vy
    wal
    #
    wa
    vx
    cv
    #
    c0
    wne
    #
    @1
    wa
    vx
    inf1.1
    @0
    @3
    @1
    @2
    vy
    cv
    ne0i
    anim1i
    eximii
end
