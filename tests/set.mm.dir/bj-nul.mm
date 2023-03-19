include "c0.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wel.mm"
include "wn.mm"
include "wal.mm"
include "isset.mm"
include "eq0.mm"
include "exbii.mm"
include "bitri.mm"

theorem bj-nul
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( (/) e. _V <-> E. x A. y -. y e. x )

  proof
    c0
    cvv
    wcel
    vx
    cv
    #
    c0
    wceq
    #
    vx
    wex
    vy
    vx
    wel
    wn
    vy
    wal
    #
    vx
    wex
    vx
    c0
    isset
    @1
    @2
    vx
    vy
    @0
    eq0
    exbii
    bitri
end
