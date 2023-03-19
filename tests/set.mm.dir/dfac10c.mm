include "wac.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "dfac10.mm"
include "eqv.mm"
include "isnum2.mm"
include "albii.mm"
include "3bitri.mm"

theorem dfac10c
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( CHOICE <-> A. x E. y e. On y ~~ x )

  proof
    wac
    ccrd
    cdm
    #
    cvv
    wceq
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wal
    vy
    cv
    @1
    cen
    wbr
    vy
    con0
    wrex
    #
    vx
    wal
    dfac10
    vx
    @0
    eqv
    @2
    @3
    vx
    vy
    @1
    isnum2
    albii
    3bitri
end
