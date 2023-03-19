include "weq.mm"
include "wex.mm"
include "wn.mm"
include "wal.mm"
include "ax6v.mm"
include "df-ex.mm"
include "mpbir.mm"

theorem ax6ev
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- E. x x = y

  proof
    vx
    vy
    weq
    #
    vx
    wex
    @0
    wn
    vx
    wal
    wn
    vx
    vy
    ax6v
    @0
    vx
    df-ex
    mpbir
end
