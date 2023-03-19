include "cv.mm"
include "ccoss.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wrel.mm"
include "wb.mm"
include "cvv.mm"
include "brcosscnvcoss.mm"
include "el2v.mm"
include "biimpi.mm"
include "gen2.mm"
include "relcoss.mm"
include "pm3.2i.mm"

theorem symrelcoss3
  let vx: setvar x
  let vy: setvar y
  let cR: class R


  assert |- ( A. x A. y ( x ,~ R y -> y ,~ R x ) /\ Rel ,~ R )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cR
    ccoss
    #
    wbr
    #
    @1
    @0
    @2
    wbr
    #
    wi
    #
    vy
    wal
    vx
    wal
    @2
    wrel
    @5
    vx
    vy
    @3
    @4
    @3
    @4
    wb
    vx
    vy
    @0
    @1
    cR
    cvv
    cvv
    brcosscnvcoss
    el2v
    biimpi
    gen2
    cR
    relcoss
    pm3.2i
end
