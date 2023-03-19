include "weq.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "ax13lem1.mm"
include "19.2.mm"
include "syl6.mm"

theorem wl-19.8eqv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( -. x = y -> ( z = y -> E. x z = y ) )

  proof
    vx
    vy
    weq
    wn
    vz
    vy
    weq
    #
    @0
    vx
    wal
    @0
    vx
    wex
    vx
    vy
    vz
    ax13lem1
    @0
    vx
    19.2
    syl6
end
