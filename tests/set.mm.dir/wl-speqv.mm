include "weq.mm"
include "wal.mm"
include "wex.mm"
include "wn.mm"
include "19.2.mm"
include "ax13lem2.mm"
include "syl5.mm"

theorem wl-speqv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( -. x = y -> ( A. x z = y -> z = y ) )

  proof
    vz
    vy
    weq
    #
    vx
    wal
    @0
    vx
    wex
    vx
    vy
    weq
    wn
    @0
    @0
    vx
    19.2
    vx
    vy
    vz
    ax13lem2
    syl5
end
