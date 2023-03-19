include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wn.mm"
include "sp.mm"
include "axc9.mm"
include "syl7.mm"
include "axc11r.mm"
include "axc11.mm"
include "pm2.43i.mm"
include "syl5.mm"
include "pm2.61ii.mm"
include "axc4i.mm"
include "ax-11.mm"
include "syl.mm"

theorem hbae
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> A. z A. x x = y )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    @0
    vz
    wal
    #
    vx
    wal
    @1
    vz
    wal
    @0
    @2
    vx
    vz
    vx
    weq
    vz
    wal
    #
    vz
    vy
    weq
    vz
    wal
    #
    @1
    @2
    wi
    @1
    @0
    @3
    wn
    @4
    wn
    @2
    @0
    vx
    sp
    vx
    vy
    vz
    axc9
    syl7
    @0
    vx
    vz
    axc11r
    @1
    @0
    vy
    wal
    #
    @4
    @2
    @1
    @5
    @0
    vx
    vy
    axc11
    pm2.43i
    @0
    vy
    vz
    axc11r
    syl5
    pm2.61ii
    axc4i
    @0
    vx
    vz
    ax-11
    syl
end
