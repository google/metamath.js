include "cv.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wal.mm"
include "wwe.mm"
include "wex.mm"
include "cvv.mm"
include "wceq.mm"
include "wac.mm"
include "ween.mm"
include "albii.mm"
include "eqv.mm"
include "dfac8.mm"
include "3bitr4ri.mm"

theorem dfac10
  let vx: setvar x
  let vy: setvar y


  assert |- ( CHOICE <-> dom card = _V )

  proof
    vx
    cv
    #
    ccrd
    cdm
    #
    wcel
    #
    vx
    wal
    @0
    vy
    cv
    wwe
    vy
    wex
    #
    vx
    wal
    @1
    cvv
    wceq
    wac
    @2
    @3
    vx
    @0
    vy
    ween
    albii
    vx
    @1
    eqv
    vx
    vy
    dfac8
    3bitr4ri
end
