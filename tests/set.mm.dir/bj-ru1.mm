include "cv.mm"
include "wel.mm"
include "wn.mm"
include "cab.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "bj-ru0.mm"
include "bj-abeq2.mm"
include "mtbir.mm"
include "nex.mm"

theorem bj-ru1
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- -. E. y y = { x | -. x e. x }

  proof
    vy
    cv
    #
    vx
    vx
    wel
    wn
    #
    vx
    cab
    wceq
    #
    vy
    @2
    vx
    vy
    wel
    @1
    wb
    vx
    wal
    vx
    vy
    bj-ru0
    @1
    vx
    @0
    bj-abeq2
    mtbir
    nex
end
