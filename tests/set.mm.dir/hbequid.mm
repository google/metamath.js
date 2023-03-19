include "weq.mm"
include "wal.mm"
include "wi.mm"
include "ax-c9.mm"
include "ax7.mm"
include "pm2.43i.mm"
include "alimi.mm"
include "a1d.mm"
include "pm2.61ii.mm"

theorem hbequid
  let vx: setvar x
  let vy: setvar y


  assert |- ( x = x -> A. y x = x )

  proof
    vy
    vx
    weq
    #
    vy
    wal
    #
    @1
    vx
    vx
    weq
    #
    @2
    vy
    wal
    #
    wi
    vx
    vx
    vy
    ax-c9
    @1
    @3
    @2
    @0
    @2
    vy
    @0
    @2
    vy
    vx
    vx
    ax7
    pm2.43i
    alimi
    a1d
    #
    @4
    pm2.61ii
end
