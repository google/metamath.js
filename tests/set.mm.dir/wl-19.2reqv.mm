include "weq.mm"
include "wn.mm"
include "wex.mm"
include "wal.mm"
include "ax13lem2.mm"
include "ax13lem1.mm"
include "syld.mm"

theorem wl-19.2reqv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( -. x = y -> ( E. x z = y -> A. x z = y ) )

  proof
    vx
    vy
    weq
    wn
    vz
    vy
    weq
    #
    vx
    wex
    @0
    @0
    vx
    wal
    vx
    vy
    vz
    ax13lem2
    vx
    vy
    vz
    ax13lem1
    syld
end
