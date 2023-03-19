include "crels.mm"
include "wcel.mm"
include "ccnv.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "wal.mm"
include "elrelscnveq.mm"
include "elrelscnveq2.mm"
include "bitrd.mm"

theorem elrelscnveq4
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( R e. Rels -> ( `' R C_ R <-> A. x A. y ( x R y <-> y R x ) ) )

  proof
    cR
    crels
    wcel
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
    elrelscnveq
    vx
    vy
    cR
    elrelscnveq2
    bitrd
end
