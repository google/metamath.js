include "weq.mm"
include "wal.mm"
include "ax-c11.mm"
include "pm2.43i.mm"
include "equcomi1.mm"
include "alimi.mm"
include "syl.mm"

theorem aecom-o
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y -> A. y y = x )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    @0
    vy
    wal
    #
    vy
    vx
    weq
    #
    vy
    wal
    @1
    @2
    @0
    vx
    vy
    ax-c11
    pm2.43i
    @0
    @3
    vy
    vx
    vy
    equcomi1
    alimi
    syl
end
