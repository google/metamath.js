include "weq.mm"
include "wex.mm"
include "wn.mm"
include "wal.mm"
include "ax6e.mm"
include "df-ex.mm"
include "mpbi.mm"

theorem ax6
  let vx: setvar x
  let vy: setvar y


  assert |- -. A. x -. x = y

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
    ax6e
    @0
    vx
    df-ex
    mpbi
end
