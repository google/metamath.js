include "weq.mm"
include "wal.mm"
include "wi.mm"
include "ax-c9.mm"
include "ax-c16.mm"
include "pm2.61ii.mm"

theorem ax5eq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( x = y -> A. z x = y )

  proof
    vz
    vx
    weq
    vz
    wal
    vz
    vy
    weq
    vz
    wal
    vx
    vy
    weq
    #
    @0
    vz
    wal
    wi
    vx
    vy
    vz
    ax-c9
    @0
    vz
    vx
    ax-c16
    @0
    vz
    vy
    ax-c16
    pm2.61ii
end
