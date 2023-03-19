include "wrel.mm"
include "ccnv.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "wal.mm"
include "relcnveq.mm"
include "relcnveq2.mm"
include "bitrd.mm"

theorem relcnveq4
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( Rel R -> ( `' R C_ R <-> A. x A. y ( x R y <-> y R x ) ) )

  proof
    cR
    wrel
    cR
    ccnv
    #
    cR
    wss
    @0
    cR
    wceq
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    @2
    @1
    cR
    wbr
    wb
    vy
    wal
    vx
    wal
    cR
    relcnveq
    vx
    vy
    cR
    relcnveq2
    bitrd
end
