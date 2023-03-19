include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wn.mm"
include "ax-c5.mm"
include "ax-c9.mm"
include "syl7.mm"
include "ax-c11.mm"
include "aecoms-o.mm"
include "pm2.43i.mm"
include "syl5.mm"
include "pm2.61ii.mm"
include "axc4i-o.mm"
include "ax-11.mm"
include "syl.mm"

theorem hbae-o
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
    #
    @1
    @0
    @3
    wn
    @4
    wn
    @2
    @0
    vx
    ax-c5
    vx
    vy
    vz
    ax-c9
    syl7
    @5
    vx
    vz
    @0
    vx
    vz
    ax-c11
    aecoms-o
    @5
    vy
    vz
    @1
    @0
    vy
    wal
    #
    vy
    vz
    weq
    vy
    wal
    @2
    @1
    @6
    @0
    vx
    vy
    ax-c11
    pm2.43i
    @0
    vy
    vz
    ax-c11
    syl5
    aecoms-o
    pm2.61ii
    axc4i-o
    @0
    vx
    vz
    ax-11
    syl
end
