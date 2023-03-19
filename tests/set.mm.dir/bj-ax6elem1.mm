include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "axc9.mm"
include "axc16.mm"
include "pm2.61d2.mm"

theorem bj-ax6elem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( -. A. x x = y -> ( y = z -> A. x y = z ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    vx
    vz
    weq
    vx
    wal
    vy
    vz
    weq
    #
    @0
    vx
    wal
    wi
    vy
    vz
    vx
    axc9
    @0
    vx
    vz
    axc16
    pm2.61d2
end
