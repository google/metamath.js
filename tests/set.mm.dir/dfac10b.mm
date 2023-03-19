include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "wal.mm"
include "cima.mm"
include "wcel.mm"
include "wac.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "elima.mm"
include "bicomi.mm"
include "albii.mm"
include "dfac10c.mm"
include "eqv.mm"
include "3bitr4i.mm"

theorem dfac10b
  let vx: setvar x
  let vy: setvar y


  assert |- ( CHOICE <-> ( ~~ " On ) = _V )

  proof
    vy
    cv
    vx
    cv
    #
    cen
    wbr
    vy
    con0
    wrex
    #
    vx
    wal
    @0
    cen
    con0
    cima
    #
    wcel
    #
    vx
    wal
    wac
    @2
    cvv
    wceq
    @1
    @3
    vx
    @3
    @1
    vy
    @0
    cen
    con0
    vx
    vex
    elima
    bicomi
    albii
    vx
    vy
    dfac10c
    vx
    @2
    eqv
    3bitr4i
end
